open test_compilerLib
(*
open numML
val code = stackshift (fromInt 1) (fromInt 2)
val [a,b,c,d,e] = map (Number o intML.fromInt) [0,1,2,3,4]
val [v,w,x,y,z] = map (Number o intML.fromInt) [10,11,12,13,14]
val [s,t,u] = map (Number o intML.fromInt) [20,21,22]
val bs = bc_state ([a,v,w,s,t,u],map Stack code,ZERO,fmapML.FEMPTY,ZERO,"",[],(fn _ => ZERO),NONE)
print_bs (valOf (bc_eval bs))
*)
val e1 = ``Lit (IntLit 42)``
val (m,[r as Number i]) = mst_run_exp e1
val SOME 42 = intML.toInt i;
val true = (OLit (IntLit (intML.fromInt 42))) = (bv_to_ov m r)
val e2 = ``If (Lit (Bool T)) (Lit (IntLit 1)) (Lit (IntLit 2))``
val [Number i] = run_exp e2
val SOME 1 = intML.toInt i;
val e3 = ``If (Lit (Bool F)) (Lit (IntLit 1)) (Lit (IntLit 2))``
val [Number i] = run_exp e3
val SOME 2 = intML.toInt i;
val e4 = ``App Equality (Lit (IntLit 1)) (Lit (IntLit 2))``
val (m,[v]) = mst_run_exp e4
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e5 = ``Fun "x" (Var (Short "x"))``
val (m,[f]) = mst_run_exp e5
val true = OFn = bv_to_ov m f;
val e6 = ``Let "x" (Lit (IntLit 1)) (App (Opn Plus) (Var (Short "x")) (Var (Short "x")))``
val [Number i] = run_exp e6
val SOME 2 = intML.toInt i;
val e7 = ``Let "x" (Lit (IntLit 1))
             (Let "y" (Lit (IntLit 2))
                (Let "x" (Lit (IntLit 3))
                   (App (Opn Plus) (Var (Short "x")) (Var (Short "y")))))``
val [Number i] = run_exp e7
val SOME 5 = intML.toInt i;
val e8 = ``
Let "0?" (Fun "x" (App Equality (Var (Short "x")) (Lit (IntLit 0))))
  (Let "x" (Lit (IntLit 1))
    (Let "x" (App (Opn Minus) (Var (Short "x")) (Var (Short "x")))
      (App Opapp (Var (Short "0?")) (Var (Short "x")))))``
val (m,[v]) = mst_run_exp e8
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e9 = ``
Let "1?" (Fun "x" (App Equality (Var (Short "x")) (Lit (IntLit 1))))
  (Let "x" (Lit (IntLit 1))
    (Let "x" (App (Opn Minus) (Var (Short "x")) (Var (Short "x")))
      (App Opapp (Var (Short "1?")) (Var (Short "x")))))``
val (m,[v]) = mst_run_exp e9
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e10 = ``
Let "x" (Lit (IntLit 3))
(If (App (Opb Gt) (Var (Short "x")) (App (Opn Plus) (Var (Short "x")) (Var (Short "x"))))
  (Var (Short "x")) (Lit (IntLit 4)))``
val [Number i] = run_exp e10
val SOME 4 = intML.toInt i;
val e11 = ``
Let "x" (Lit (IntLit 3))
(If (App (Opb Geq) (Var (Short "x")) (Var (Short "x")))
  (Var (Short "x")) (Lit (IntLit 4)))``
val [Number i] = run_exp e11
val SOME 3 = intML.toInt i;
val e12 = ``
Let "lt2" (Fun "x" (App (Opb Lt) (Var (Short "x")) (Lit (IntLit 2))))
  (App Opapp (Var (Short "lt2")) (Lit (IntLit 3)))``
val (m,[v]) = mst_run_exp e12
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e13 = ``
Let "lq2" (Fun "x" (App (Opb Leq) (Var (Short "x")) (Lit (IntLit 2))))
  (App Opapp (Var (Short "lq2")) (Lit (IntLit 0)))``
val (m,[v]) = mst_run_exp e13
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e14 = ``
Let "x" (Lit (IntLit 0))
  (Let "y" (App (Opn Plus) (Var (Short "x")) (Lit (IntLit 2)))
    (If (App (Opb Geq) (Var (Short "y")) (Var (Short "x")))
      (Var (Short "x")) (Lit (IntLit 4))))``
val [Number i] = run_exp e14
val SOME 0 = intML.toInt i;
val e15 = ``
Let "x" (Lit (Bool T))
(App Equality
  (Mat (Var (Short "x"))
    [(Plit (Bool F), (Lit (IntLit 1)));
     (Pvar "y", (Var (Short "y")))])
  (Var (Short "x")))``
val (m,[v]) = mst_run_exp e15
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e16 = ``App Equality (Let "x" (Lit (Bool T)) (Var (Short "x"))) (Lit (Bool F))``
val (m,[v]) = mst_run_exp e16
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e17 = ``App Equality
  (Let "f" (Fun "_" (Lit (Bool T))) (App Opapp (Var (Short "f")) (Lit (Bool T))))
  (Lit (Bool F))``
val (m,[v]) = mst_run_exp e17
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e18 = ``
Let "x" (Lit (Bool T))
  (App Equality
    (Let "f" (Fun "_" (Var (Short "x"))) (App Opapp (Var (Short "f")) (Var (Short "x"))))
    (Var (Short "x")))``
val (m,[v]) = mst_run_exp e18
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e19 = ``
Let "x" (Lit (Bool T))
  (App Opapp (Fun "_" (Var (Short "x"))) (Lit (Bool F)))``
val (m,[v]) = mst_run_exp e19
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e20 = ``
Let "f" (Fun "_" (Lit (Bool T)))
(App Equality
  (App Opapp (Var (Short "f")) (Lit (Bool T)))
  (Lit (Bool F)))``
val (m,[v]) = mst_run_exp e20
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e21 = ``Let "x" (Lit (Bool T))
(App Equality
  (Let "f" (Fun "_" (Var (Short "x")))
    (App Opapp (Var (Short "f")) (Var (Short "x"))))
  (Var (Short "x")))``
val (m,[v]) = mst_run_exp e21
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e22 = ``Con (SOME (Short "::")) [Lit (Bool T); Con (SOME (Short "nil")) []]``
val (bs,rs) = run_decs inits []
val (m,[Block (t1,[v,Block (t2,[])])]) = mst_run_decs_exp ([],e22)
val true = (OConv(SOME(Short"nil"),[])) = (bv_to_ov m ((Block (t2,[]))))
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e23 = ``Mat (Con (SOME (Short "::")) [Lit (IntLit 2);
                 Con (SOME (Short "::")) [Lit (IntLit 3);
                 Con (SOME (Short "nil")) []]])
            [(Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"],
              Var (Short "x"));
             (Pcon (SOME (Short "nil")) [],
              Lit (IntLit 1))]``
val [Number i] = run_decs_exp ([],e23)
val SOME 2 = intML.toInt i;
val e24 = ``Mat (Con (SOME (Short "nil")) [])
            [(Pcon (SOME (Short "nil")) [], Lit (Bool F))]``
val (m,[v]) = mst_run_decs_exp([],e24)
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e25 = ``Mat (Con (SOME (Short "::")) [Lit (IntLit 2);
                 Con (SOME (Short "nil")) []])
            [(Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs"],
              Var (Short "x"))]``
val [Number i] = run_decs_exp([],e25)
val SOME 2 = intML.toInt i;
val e26 = ``Mat (Con (SOME (Short "::")) [Lit (IntLit 2);
                 Con (SOME (Short "nil")) []])
            [(Pcon (SOME (Short "::")) [Plit (IntLit 2);
              Pcon (SOME (Short "nil")) []],
              Lit (IntLit 5))]``
val [Number i] = run_decs_exp([],e26)
val SOME 5 = intML.toInt i;
(*
val e27 =
CLetfun(false,["1"],[([],sumML.INL (CRaise Bind_error))],
CIf(CPrim2(CEq,CLit (IntLit i0),CLit (IntLit i0)),
    CLit (IntLit i1),
    CCall (CVar (Short "1"),[])))
val (bs,rs) = inits
val rs = compile_Cexp rs e27
val bs = add_code rs bs
val bs = bc_eval bs
val [Number i] = bc_state_stack bs
val SOME 1 = intML.toInt i;
*)
val e28 = ``
Letrec [("fac",("n",
  If (App Equality (Var (Short "n")) (Lit (IntLit 0)))
     (Lit (IntLit 1))
     (App (Opn Times)
       (Var (Short "n"))
       (App Opapp (Var (Short "fac")) (App (Opn Minus)
                                   (Var (Short "n"))
                                   (Lit (IntLit 1)))))))]
  (App Opapp (Var (Short "fac")) (Lit (IntLit 5)))``
val [Number i] = run_exp e28
val SOME 120 = intML.toInt i;
val d = ``Dlet (Pvar "Foo") (Lit (IntLit 42))``
val e41 = ``Var (Short "Foo")``
val [Number i,Number j] = run_decs_exp([d],e41)
val SOME 42 = intML.toInt i;
val true = i = j;
val d = ``Dletrec [("I","x",(Var (Short "x")))]``
val e42 = ``App Opapp (Var (Short "I")) (Lit (IntLit 42))``
val [Number i,cl] = run_decs_exp([d],e42)
val SOME 42 = intML.toInt i;
val d0 = ``
Dletrec
  [("N","v1",
    If (App (Opb Gt) (Var (Short "v1")) (Lit (IntLit 100)))
      (App (Opn Minus) (Var (Short "v1")) (Lit (IntLit 10)))
      (App Opapp (Var (Short "N"))
         (App Opapp (Var (Short "N"))
            (App (Opn Plus) (Var (Short "v1")) (Lit (IntLit 11))))))]
``
val e29 = ``App Opapp (Var (Short "N")) (Lit (IntLit 42))``
val [Number i,cl] = run_decs_exp([d0],e29)
val SOME 91 = intML.toInt i;
val e35 = ``Let "f" (Fun "x" (Fun "y" (App (Opn Plus) (Var (Short "x")) (Var (Short "y"))))) (App Opapp (App Opapp (Var (Short "f")) (Lit (IntLit 2))) (Lit (IntLit 3)))``
val [Number i] = run_exp e35
val SOME 5 = intML.toInt i;
val e36 = ``Letrec [("f", ("x", (Fun "y" (App (Opn Plus) (Var (Short "x")) (Var (Short "y"))))))] (App Opapp (App Opapp (Var (Short "f")) (Lit (IntLit 2))) (Lit (IntLit 3)))``
val [Number i] = run_exp e36
val SOME 5 = intML.toInt i;
val e37 = ``Letrec [("z", ("x", (Mat (Var (Short "x")) [(Plit (IntLit 0), (Var (Short "x")));(Pvar "y", App Opapp (Var (Short "z")) (App (Opn Minus) (Var (Short "x")) (Var (Short "y"))))])))] (App Opapp (Var (Short "z")) (Lit (IntLit 5)))``
val [Number i] = run_exp e37
val SOME 0 = intML.toInt i;
val e38 = ``Let "z" (Fun "x" (Mat (Var (Short "x")) [(Plit (IntLit 0), (Var (Short "x")));(Pvar "y", (App (Opn Minus) (Var (Short "x")) (Var (Short "y"))))])) (App Opapp (Var (Short "z")) (Lit (IntLit 5)))``
val [Number i] = run_exp e38
val SOME 0 = intML.toInt i;
val e39 = ``Letrec [("z", ("x", (Mat (Var (Short "x")) [(Plit (IntLit 0), (Var (Short "x")));(Pvar "y", (App (Opn Minus) (Var (Short "x")) (Var (Short "y"))))])))] (App Opapp (Var (Short "z")) (Lit (IntLit 5)))``
val [Number i] = run_exp e39
val SOME 0 = intML.toInt i;
val paird = ``
Dtype [(["'a"; "'b"],"prod",[("Pair_type",[Tvar "'a"; Tvar "'b"])])]
``
val _ = reset_translation()
val _ = translate listTheory.APPEND
val _ = finalise_translation()
val ds = dest_list I (get_decls())
val e33 = ``App Opapp (Var (Short "APPEND")) (Con (SOME (Short "nil")) [])``
val (m,st) = mst_run_decs_exp (ds,e33)
val tm = bv_to_ov m (hd st)
val true = tm = OFn;
val e34 = ``App Opapp (App Opapp (Var (Short "APPEND")) (Con (SOME (Short "nil")) []))
                      (Con (SOME (Short "nil")) [])``
val (m,st) = mst_run_decs_exp (ds,e34)
val [r,cl] = st
val tm = bv_to_ov m r
val true = tm = OConv (SOME (Short"nil"),[])
val tm = bv_to_ov m cl
val true = tm = OFn;
fun h t = hd(tl(snd(strip_comb(concl t))))
val t = hol2deep ``[1;2;3]++[4;5;6:num]``
val e30 = h t
val (m,st) = mst_run_decs_exp (ds,e30)
val [res,cl] = st
val tm = bv_to_ov m res
val true = tm = term_to_ov (hol2val ``[1;2;3;4;5;6:num]``);
val t = hol2deep ``[]++[4:num]``
val e32 = h t
val (m,st) = mst_run_decs_exp (ds,e32)
val [res,cl] = st
val tm = bv_to_ov m res
val true = tm = OConv (SOME (Short"::"),[OLit (IntLit (intML.fromInt 4)), OConv (SOME (Short"nil"),[])]);
val _ = reset_translation()
val _ = translate listTheory.APPEND
val _ = translate sortingTheory.PART_DEF
val _ = translate sortingTheory.PARTITION_DEF
val _ = translate sortingTheory.QSORT_DEF
val _ = finalise_translation()
val ds = dest_list I (get_decls())
val t = hol2deep ``QSORT (λx y. x ≤ y) [9;8;7;6;2;3;4;5:num]``
val e31 = h t;
val (m,st) = mst_run_decs_exp (ds,e31)
val [res,clQSORT,clAPPEND,clPARTITION,clPART] = st
val tm = bv_to_ov m res
val true = tm = term_to_ov(hol2val ``[2;3;4;5;6;7;8;9:num]``);
val d = ``
Dlet (Pvar "add1")
  (Fun "x" (App (Opn Plus) (Var (Short "x")) (Lit (IntLit 1))))``
val e40 = ``App Opapp (Var (Short "add1")) (Lit (IntLit 1))``
val (m,st) = mst_run_decs_exp ([d],e40)
val [res,add1] = st
val true = bv_to_ov m res = term_to_ov(hol2val ``2:int``);
val e43 = ``Letrec [("o","n",
  If (App Equality (Var (Short "n")) (Lit (IntLit 0)))
     (Var (Short "n"))
     (App Opapp
       (Var (Short "o"))
       (App (Opn Minus) (Var (Short "n")) (Lit (IntLit 1)))))]
  (App Opapp (Var (Short "o")) (Lit (IntLit 1000)))``
val (bs43,_,_) = prep_exp inits e43
val SOME s43 = bc_eval_limit 13 bs43
val [Number z] = bc_state_stack s43
val SOME 0 = intML.toInt z;
val d = ``Dletrec
[("o","n",
  If (App Equality (Var (Short "n")) (Lit (IntLit 0)))
     (Var (Short "n"))
     (App Opapp
       (Var (Short "o"))
       (App (Opn Minus) (Var (Short "n")) (Lit (IntLit 1)))))]``
val e44 = ``App Opapp (Var (Short "o")) (Lit (IntLit 1000))``
val [Number i, cl] = run_decs_exp ([d],e44)
val SOME 0 = intML.toInt i;
val d0 = paird
val d1 = ``Dlet (Pcon (SOME (Short "Pair_type")) [Pvar "x";Pvar "y"]) (Con (SOME (Short "Pair_type")) [Lit (IntLit 1);Lit (IntLit 2)])``
val d2 = ``Dlet (Pvar "x") (Lit (IntLit 3))``
val e45 = ``Con (SOME (Short "Pair_type")) [Var (Short "x");Var (Short "y")]``
val [Block (_,[Number xb,Number yb]),Number x2,Number x1,Number y] = run_decs_exp ([d0,d1,d2],e45)
val SOME 3 = intML.toInt xb
val SOME 2 = intML.toInt yb
val true = xb = x2
(*val true = yb = y; NOT SURE *)
val d1 = ``Dlet (Pcon (SOME (Short "Pair_type")) [Pvar "y";Pvar "x"]) (Con (SOME (Short "Pair_type")) [Lit (IntLit 1);Lit (IntLit 2)])``
val d2 = ``Dlet (Pvar "x") (Lit (IntLit 3))``
val e46 = ``Con (SOME (Short "Pair_type")) [Var (Short "x");Var (Short "y")]``
val [Block (_,[Number xb,Number yb]),Number x2,Number y,Number x1] = run_decs_exp ([d0,d1,d2],e46)
val SOME 3 = intML.toInt xb
val SOME 1 = intML.toInt yb
val true = x2 = xb
(*val true = y = yb; NOT SURE *)
val d0 = paird
val d1 = ``Dlet (Pcon (SOME (Short "Pair_type")) [Pvar "x";Pvar "y"]) (Con (SOME (Short "Pair_type")) [Lit (IntLit 1);Lit (IntLit 2)])``
val d2 = ``Dlet (Pvar "x") (Lit (IntLit 3))``
val d3 = ``Dlet (Pvar "y") (Lit (IntLit 4))``
val e47 = ``Con (SOME (Short "Pair_type")) [
              Con (SOME (Short "Pair_type")) [Var (Short "x"); Var (Short "y")];
              Let "x" (Fun "x" (App (Opn Plus) (Var (Short "x")) (Var (Short "y"))))
                (App Opapp (Var (Short "x")) (Var (Short "y")))]``
val [Block (_,[Block (_,[Number x3,Number y4]),Number yy]),Number y2,Number x2,Number x1,Number y1] = run_decs_exp([d0,d1,d2,d3],e47)
val SOME 4 = intML.toInt y2
val SOME 3 = intML.toInt x2
val SOME 3 = intML.toInt x3
val SOME 4 = intML.toInt y4
val SOME 8 = intML.toInt yy;
val d0 = ``Dlet (Pvar "x") (Let "x" (Lit (IntLit 1)) (App (Opn Minus) (Var (Short "x")) (Var (Short "x"))))``
val e48 = ``Var (Short "x")``
val [Number xv,Number xd] = run_decs_exp([d0],e48)
val SOME 0 = intML.toInt xv
val SOME 0 = intML.toInt xd;
val d0 = ``Dlet (Pvar "x") (Let "x" (Lit (IntLit 1)) (App (Opn Minus) (Var (Short "x")) (Var (Short "x"))))``
val d1 = ``Dlet (Pvar "x") (App (Opn Minus) (Var (Short "x")) (Let "x" (Lit (IntLit 1)) (Var (Short "x"))))``
val e49 = ``App (Opn Times) (Var (Short "x")) (Let "x" (Lit (IntLit (-1))) (Var (Short "x")))``
val [Number r,Number x2,Number x1] = run_decs_exp([d0,d1],e49)
val SOME ~1 = intML.toInt x2
val SOME 1 = intML.toInt r;
val d0 = paird
val d1 = ``Dlet (Pcon (SOME (Short "Pair_type")) [Pvar "y";Pvar "x"]) (Con (SOME (Short "Pair_type")) [Lit (IntLit 1);Lit (IntLit 2)])``
val e50 = ``Var (Short "y")``
val [Number r, Number y, Number x] = run_decs_exp([d0,d1],e50)
(*
val SOME 2 = intML.toInt x
val SOME 1 = intML.toInt y
NOT SURE
*)
val SOME 1 = intML.toInt r;
val d0 = ``Dlet (Pvar "x") (Lit (IntLit 1))``
val d1 = ``Dtype [([],"unit",[("()",[])])]``
val d2 = ``Dlet (Pvar "f") (Fun " " (Mat (Var (Short " ")) [(Pcon (SOME (Short "()")) [],App (Opn Plus) (Var (Short "x")) (Lit (IntLit 1)))]))``
val d3 = ``Dlet (Pvar "x") (Lit (IntLit 100))``
val e51 = ``App Opapp (Var (Short "f")) (Con (SOME (Short "()")) [])``
val [Number r, Number x2, _, Number x1] = run_decs_exp([d0,d1,d2,d3],e51)
val SOME 2 = intML.toInt r
val SOME 100 = intML.toInt x2;
val d0 = paird
val e52 = ``Let "x" (Con (SOME (Short "Pair_type")) [Lit (IntLit 1);Lit (IntLit 2)])
  (Mat (Var (Short "x"))
      [(Pcon (SOME (Short "Pair_type")) [Pvar "x";Plit (IntLit 2)], Lit (IntLit 1))])``
val [Number r] = run_decs_exp([d0],e52)
val SOME 1 = intML.toInt r;
val d0 = paird
val e53 = ``Let "x" (Con (SOME (Short "Pair_type")) [Lit (IntLit 1);Con (SOME (Short "Pair_type")) [Lit (IntLit 2); Lit (IntLit 3)]])
  (Mat (Var (Short "x"))
      [(Pcon (SOME (Short "Pair_type")) [Pvar "x";Pcon (SOME (Short "Pair_type")) [Pvar "y";Pvar "z"]], Var (Short "y"))])``
val [Number r] = run_decs_exp([d0],e53)
val SOME 2 = intML.toInt r;
val e54 = ``Letrec [
  ("x","x",App (Opn Plus) (Var (Short "x")) (Lit (IntLit 1)));
  ("f","y",App Opapp (Var (Short "x")) (Var (Short "y")))]
    (App Opapp (Var (Short "f")) (Lit (IntLit 1)))``
val [Number r] = run_exp e54
val SOME 2 = intML.toInt r;
val e55 = ``Letrec [
  ("f","y",App Opapp (Var (Short "x")) (Var (Short "y")));
  ("x","x",App (Opn Plus) (Var (Short "x")) (Lit (IntLit 1)))]
    (App Opapp (Var (Short "f")) (Lit (IntLit 1)))``
val [Number r] = run_exp e55
val SOME 2 = intML.toInt r;
val e56 = ``Letrec [
  ("x","x",App (Opn Plus) (Var (Short "x")) (Lit (IntLit 1)))]
    (App Opapp (Var (Short "x")) (Lit (IntLit 1)))``
val [Number r] = run_exp e56
val SOME 2 = intML.toInt r;
val e57 = ``Letrec [
  ("f","y",App Opapp (Var (Short "g")) (Var (Short "y")));
  ("g","x",App (Opn Plus) (Var (Short "x")) (Lit (IntLit 1)))]
    (App Opapp (Var (Short "f")) (Lit (IntLit 1)))``
val [Number r] = run_exp e57
val SOME 2 = intML.toInt r;
val e58 = ``Letrec [
  ("g","x",App (Opn Plus) (Var (Short "x")) (Lit (IntLit 1)));
  ("f","y",App Opapp (Var (Short "g")) (Var (Short "y")))]
    (App Opapp (Var (Short "f")) (Lit (IntLit 1)))``
val [Number r] = run_exp e58
val SOME 2 = intML.toInt r;
val e59 = ``Let "x" (Lit (IntLit 2))
  (Letrec [
    ("x","x",App (Opn Plus) (Var (Short "x")) (Lit (IntLit 1)));
    ("f","y",App Opapp (Var (Short "x")) (Var (Short "y")))]
      (App Opapp (Var (Short "f")) (Lit (IntLit 1))))``
val [Number r] = run_exp e59
val SOME 2 = intML.toInt r;
val e60 = ``Let "i" (Lit (IntLit 10))
  (Let "1" (Lit (IntLit 1))
    (Letrec [
("z","j",App Equality (Var (Short "j")) (Lit (IntLit 0)));
("f0","i",If (App Opapp (Var (Short "z")) (Var (Short "i"))) (Lit (Bool T))
         (App Opapp (Var (Short "f2")) (App Opapp (Var (Short "s")) (Var (Short "i")))));
("f1","i",If (App Opapp (Var (Short "z")) (Var (Short "i"))) (Lit (Bool F))
         (App Opapp (Var (Short "f0")) (App Opapp (Var (Short "s")) (Var (Short "i")))));
("f2","i",If (App Opapp (Var (Short "z")) (Var (Short "i"))) (Lit (Bool F))
         (App Opapp (Var (Short "f1")) (App Opapp (Var (Short "s")) (Var (Short "i")))));
("s","k",App (Opn Minus) (Var (Short "k")) (Var (Short "1")))]
  (App Opapp (Var (Short "f0")) (Var (Short "i")))))``
val (m,[r]) = mst_run_exp e60
val true = (OLit (Bool false)) = bv_to_ov m r;
val d0 = ``Dlet (Pvar "1") (Lit (IntLit 1))``
val d1 = ``Dletrec [
("z","j",App Equality (Var (Short "j")) (Lit (IntLit 0)));
("f0","i",If (App Opapp (Var (Short "z")) (Var (Short "i"))) (Lit (Bool T))
         (App Opapp (Var (Short "f2")) (App Opapp (Var (Short "s")) (Var (Short "i")))));
("f1","i",If (App Opapp (Var (Short "z")) (Var (Short "i"))) (Lit (Bool F))
         (App Opapp (Var (Short "f0")) (App Opapp (Var (Short "s")) (Var (Short "i")))));
("f2","i",If (App Opapp (Var (Short "z")) (Var (Short "i"))) (Lit (Bool F))
         (App Opapp (Var (Short "f1")) (App Opapp (Var (Short "s")) (Var (Short "i")))));
("s","k",App (Opn Minus) (Var (Short "k")) (Var (Short "1")))]``
val e61 = ``App Opapp (Var (Short "f0")) (Lit (IntLit 12))``
val (m,[r,_,_,_,_,_,_]) = mst_run_decs_exp([d0,d1],e61)
val true = (OLit (Bool true)) = bv_to_ov m r;
val e62 = ``Letrec ["f","x",Var (Short "x")] (App Opapp (Var (Short "f")) (Lit (IntLit 42)))``
val [Number r] = run_exp e62
val SOME 42 = intML.toInt r;
val e63 = ``Letrec [("f","x",App Opapp (Var (Short "g")) (Var (Short "x")));
                    ("g","x",Var (Short "x"))]
                    (App Opapp (Var (Short "f")) (Lit (IntLit 42)))``
val [Number r] = run_exp e63
val SOME 42 = intML.toInt r;
val d0 = ``Dlet (Pvar "1") (Lit (IntLit 1))``
val d1 = ``Dletrec [
("a","b",App Equality (Var (Short "b")) (Lit (IntLit 0)));
("c","d",If (App Opapp (Var (Short "a")) (Var (Short "d"))) (Lit (Bool T))
              (App Opapp (Var (Short "g")) (App Opapp (Var (Short "i")) (Var (Short "d")))));
("e","f",If (App Opapp (Var (Short "a")) (Var (Short "f"))) (Lit (Bool F))
              (App Opapp (Var (Short "c")) (App Opapp (Var (Short "i")) (Var (Short "f")))));
("g","h",If (App Opapp (Var (Short "a")) (Var (Short "h"))) (Lit (Bool F))
              (App Opapp (Var (Short "e")) (App Opapp (Var (Short "i")) (Var (Short "h")))));
("i","j",App (Opn Minus) (Var (Short "j")) (Var (Short "1")))]``
val e64 = ``App Opapp (Var (Short "c")) (Lit (IntLit 12))``
val (m,[r,_,_,_,_,_,_]) = mst_run_decs_exp([d0,d1],e64)
val true = (OLit (Bool true)) = bv_to_ov m r;
val d1 = ``Dletrec [
("a","b",App Equality (Var (Short "b")) (Lit (IntLit 0)));
("c","d",If (App Opapp (Var (Short "a")) (Var (Short "d"))) (Lit (Bool T))
         (App Opapp (Var (Short "g")) (App Opapp (Var (Short "i")) (Var (Short "d")))));
("e","f",If (App Opapp (Var (Short "a")) (Var (Short "f"))) (Lit (Bool F))
         (App Opapp (Var (Short "c")) (App Opapp (Var (Short "i")) (Var (Short "f")))));
("g","h",If (App Opapp (Var (Short "a")) (Var (Short "h"))) (Lit (Bool F))
         (App Opapp (Var (Short "e")) (App Opapp (Var (Short "i")) (Var (Short "h")))));
("i","j",App (Opn Minus) (Var (Short "j")) (Lit (IntLit 1)))]``
val e65 = ``App Opapp (Var (Short "c")) (Lit (IntLit 12))``
val (m,[r,_,_,_,_,_]) = mst_run_decs_exp([d1],e65)
val true = (OLit (Bool true)) = bv_to_ov m r;
val e66 = ``Letrec [
("a","b",App Equality (Var (Short "b")) (Lit (IntLit 0)));
("c","d",If (App Opapp (Var (Short "a")) (Var (Short "d"))) (Lit (Bool T))
         (App Opapp (Var (Short "g")) (App Opapp (Var (Short "i")) (Var (Short "d")))));
("e","f",If (App Opapp (Var (Short "a")) (Var (Short "f"))) (Lit (Bool F))
         (App Opapp (Var (Short "c")) (App Opapp (Var (Short "i")) (Var (Short "f")))));
("g","h",If (App Opapp (Var (Short "a")) (Var (Short "h"))) (Lit (Bool F))
         (App Opapp (Var (Short "e")) (App Opapp (Var (Short "i")) (Var (Short "h")))));
("i","j",App (Opn Minus) (Var (Short "j")) (Lit (IntLit 1)))]
(App Opapp (Var (Short "c")) (Lit (IntLit 12)))``
val (m,[r]) = mst_run_exp e66
val true = (OLit (Bool true)) = bv_to_ov m r;
val e67 = ``Let "x" (Lit (Bool T)) (If (Var (Short "x")) (Lit (IntLit 1)) (Lit (IntLit 2)))``
val (m,[r]) = mst_run_exp e67
val true = (OLit (IntLit (intML.fromInt 1))) = bv_to_ov m r;
val e68 = ``Letrec [
  ("not","x",Mat (Var (Short "x"))
               [(Plit (Bool T),Lit(Bool F));
                (Plit (Bool F),Lit(Bool T))])]
   (If (Let "x" (Lit (Bool T)) (App Opapp (Var (Short "not")) (Var (Short "x")))) (Lit (IntLit 1)) (Lit (IntLit 2)))``
val (m,[r]) = mst_run_exp e68
val true = (OLit (IntLit (intML.fromInt 2))) = bv_to_ov m r;
val e69 = ``Let "f"
  (Fun "x"
    (If (Lit (Bool F))
        (Let "y" (Lit (IntLit 1))
          (Var (Short "y")))
        (App Opapp (Fun "z" (Var (Short "z"))) (Lit (IntLit 2)))))
  (App Opapp (Var (Short "f")) (Lit (IntLit 0)))``
val (m,[r]) = mst_run_exp e69
val true = (OLit (IntLit (intML.fromInt 2))) = bv_to_ov m r;
val e70 = ``Let "f"
  (Fun "x"
    (If (Lit (Bool F))
        (Lit (IntLit 1))
        (App Opapp (Fun "z" (Var (Short "z"))) (Lit (IntLit 2)))))
  (App Opapp (Var (Short "f")) (Lit (IntLit 0)))``
val (m,[r]) = mst_run_exp e70
val true = (OLit (IntLit (intML.fromInt 2))) = bv_to_ov m r;
val e71 = ``Let "x" (Lit (IntLit 0))
            (App (Opb Gt) (Lit (IntLit 1)) (Var (Short "x")))``
val (m,[r]) = mst_run_exp e71
val true = (OLit (Bool true) = bv_to_ov m r);
val e72 = ``Raise (Con(SOME(Short"Bind"))[])``
val (m,[bv]) = mst_run_exp_exc e72
val true = (OConv (SOME (Short"Bind"),[])) = bv_to_ov m bv;
val e73' = ``Handle (Raise (Con(SOME(Short"Bind"))[])) [Pcon(SOME(Short"Bind"))[],Lit(IntLit 42)]``
val [Number i] = run_exp e73'
val SOME 42 = intML.toInt i;
val dint = ``Dexn "Int" [Tint]``
val e73 = ``Handle (Raise (Con(SOME(Short"Int"))[Lit(IntLit 42)])) [Pcon(SOME(Short"Int"))[Pvar "x"],Var(Short "x")]``
val [Number i] = run_decs_exp ([dint],e73)
val SOME 42 = intML.toInt i;
val e74 = ``Mat (Lit (Bool F)) [Plit (Bool T),Lit (IntLit 0)]``
val (m,[bv]) = mst_run_exp_exc e74
val true = (OConv (SOME (Short"Bind"),[])) = bv_to_ov m bv;
val e75 = ``Handle (App (Opn Divide) (Lit (IntLit 1)) (Raise (Lit(IntLit 1)))) [Pvar "x",(Var(Short "x"))]``
val (m,[Number i]) = mst_run_exp e75
val SOME 1 = intML.toInt i;
val e76 = ``App (Opn Divide) (Lit (IntLit 1)) (Lit (IntLit 0))``
val (m,[bv]) = mst_run_exp_exc e76
val true = (OConv (SOME (Short"Div"),[])) = bv_to_ov m bv;
val e76' = ``Handle (App (Opn Divide) (Lit (IntLit 1)) (Lit (IntLit 0))) [Pvar "x",(Var(Short "x"))]``
val (m,[bv]) = mst_run_exp e76'
val true = (OConv (SOME (Short"Div"),[])) = bv_to_ov m bv;
val e77 = ``Let "x" (Lit (IntLit 0)) (Handle (App (Opn Modulo) (Lit (IntLit 1)) (Var (Short "x"))) [])``
val (m,[bv]) = mst_run_exp_exc e77
val true = (OConv (SOME (Short"Div"),[])) = bv_to_ov m bv;
val e78 = ``Let "x" (Lit (IntLit 1)) (Handle (App (Opn Modulo) (Lit (IntLit 0)) (Var (Short "x"))) [])``
val (m,[Number i]) = mst_run_exp e78
val SOME 0 = intML.toInt i;
val m = ``[Dlet (Pvar "x") (Lit (IntLit 1))]``
val (bs,rs) = run_top inits (mk_Tmod "M" m)
val (bs,rs) = run_top (bs,rs) (mk_Texp ``Var(Long"M""x")``)
val [x,mx] = bc_state_stack bs
val true = (OLit(IntLit(intML.fromInt 1))) = bv_to_ov (cpam rs) x andalso x = mx;
val (bs,rs) = run_top inits (mk_Tdec ``Dlet (Pvar "x") (Lit (IntLit 2))``)
val true = "val x = 2\n" = bc_state_output bs
val (bs,rs) = run_top (bs,rs) (mk_Tmod "M" m)
val (bs,rs) = run_top (bs,rs) (mk_Texp ``App (Opn Minus) (Var (Short "x")) (Var (Long"M""x"))``)
val [r,mx,x] = bc_state_stack bs
val true = (OLit(IntLit(intML.fromInt 1))) = bv_to_ov (cpam rs) r
    andalso(OLit(IntLit(intML.fromInt 2))) = bv_to_ov (cpam rs) x
    andalso mx = r;
val d0 = paird
val d1 = ``Dlet (Pcon (SOME (Short "Pair_type")) [Pvar "x";Pvar "y"]) (Con (SOME (Short "Pair_type")) [Lit (IntLit 1);Lit (IntLit 2)])``
val (bs,rs) = run_top inits (mk_Tdec d0)
val (bs,rs) = run_top (bs,rs) (mk_Tdec d1)
val true = "Pair_type = <constructor>\nval y = 2\nval x = 1\n" = bc_state_output bs;
val m1 = ``[Dlet (Pvar "x") (Lit (IntLit 1))]``
val (bs,rs) = run_top inits (mk_Tmod "M1" m1)
val (bs,rs) = run_top (bs,rs) (mk_Texp ``Lit (IntLit 2)``)
val m2 = ``[Dlet (Pvar "x") (Lit (IntLit 3))]``
val (bs,rs) = run_top (bs,rs) (mk_Tmod "M2" m2)
val (bs,rs) = run_top (bs,rs) (mk_Texp ``Lit (IntLit 4)``)
val (bs,rs) = run_top (bs,rs) (mk_Texp ``App (Opn Plus) (App (Opn Plus) (Var(Long"M1""x")) (Var(Short"it"))) (Var(Long"M2""x"))``)
val [r,i4,m2,i2,m1] = bc_state_stack bs
val true = (OLit(IntLit(intML.fromInt 8))) = bv_to_ov (cpam rs) r;
val m1 = ``[Dlet (Pvar "x") (Lit (IntLit 1)); Dlet (Pvar "y") (Lit(IntLit 2))]``
val (bs,rs) = run_top inits (mk_Tmod "M1" m1)
val (bs,rs) = run_top (bs,rs) (mk_Tdec ``Dlet(Pvar"x")(Lit (IntLit 3))``)
val (bs,rs) = run_top (bs,rs) (mk_Tdec ``Dlet(Pvar"y")(Lit (IntLit 4))``)
val m2 = ``[Dlet (Pvar "x") (Lit (IntLit 5)); Dlet (Pvar "y") (Lit(IntLit 6))]``
val (bs,rs) = run_top (bs,rs) (mk_Tmod "M2" m2)
val (bs,rs) = run_top (bs,rs) (mk_Texp ``App (Opn Plus) (App (Opn Plus) (Var(Long"M1""y")) (Var(Short"x"))) (Var(Long"M2""x"))``)
val [r,Number im2y,Number im2x,Number iy,Number ix,Number im1y,Number im1x] = bc_state_stack bs
val SOME m1y = intML.toInt im1y
val SOME x = intML.toInt ix
val SOME m2x = intML.toInt im2x
val true = (OLit(IntLit(intML.fromInt (m1y+x+m2x)))) = bv_to_ov (cpam rs) r;
