open test_compilerLib
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
val e5 = ``Fun "x" NONE (Var "x" NONE)``
val (m,[f]) = mst_run_exp e5
val true = OFn = bv_to_ov m f;
val e6 = ``Let NONE "x" NONE (Lit (IntLit 1)) (App (Opn Plus) (Var "x" NONE) (Var "x" NONE))``
val [Number i] = run_exp e6
val SOME 2 = intML.toInt i;
val e7 = ``Let NONE "x" NONE (Lit (IntLit 1))
             (Let NONE "y" NONE (Lit (IntLit 2))
                (Let NONE "x" NONE (Lit (IntLit 3))
                   (App (Opn Plus) (Var "x" NONE) (Var "y" NONE))))``
val [Number i] = run_exp e7
val SOME 5 = intML.toInt i;
val e8 = ``
Let NONE "0?" NONE (Fun "x" NONE (App Equality (Var "x" NONE) (Lit (IntLit 0))))
  (Let NONE "x" NONE (Lit (IntLit 1))
    (Let NONE "x" NONE (App (Opn Minus) (Var "x" NONE) (Var "x" NONE))
      (App Opapp (Var "0?" NONE) (Var "x" NONE))))``
val (m,[v]) = mst_run_exp e8
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e9 = ``
Let NONE "1?" NONE (Fun "x" NONE (App Equality (Var "x" NONE) (Lit (IntLit 1))))
  (Let NONE "x" NONE (Lit (IntLit 1))
    (Let NONE "x" NONE (App (Opn Minus) (Var "x" NONE) (Var "x" NONE))
      (App Opapp (Var "1?" NONE) (Var "x" NONE))))``
val (m,[v]) = mst_run_exp e9
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e10 = ``
Let NONE "x" NONE (Lit (IntLit 3))
(If (App (Opb Gt) (Var "x" NONE) (App (Opn Plus) (Var "x" NONE) (Var "x" NONE)))
  (Var "x" NONE) (Lit (IntLit 4)))``
val [Number i] = run_exp e10
val SOME 4 = intML.toInt i;
val e11 = ``
Let NONE "x" NONE (Lit (IntLit 3))
(If (App (Opb Geq) (Var "x" NONE) (Var "x" NONE))
  (Var "x" NONE) (Lit (IntLit 4)))``
val [Number i] = run_exp e11
val SOME 3 = intML.toInt i;
val e12 = ``
Let NONE "lt2" NONE (Fun "x" NONE (App (Opb Lt) (Var "x" NONE) (Lit (IntLit 2))))
  (App Opapp (Var "lt2" NONE) (Lit (IntLit 3)))``
val (m,[v]) = mst_run_exp e12
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e13 = ``
Let NONE "lq2" NONE (Fun "x" NONE (App (Opb Leq) (Var "x" NONE) (Lit (IntLit 2))))
  (App Opapp (Var "lq2" NONE) (Lit (IntLit 0)))``
val (m,[v]) = mst_run_exp e13
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e14 = ``
Let NONE "x" NONE (Lit (IntLit 0))
  (Let NONE "y" NONE (App (Opn Plus) (Var "x" NONE) (Lit (IntLit 2)))
    (If (App (Opb Geq) (Var "y" NONE) (Var "x" NONE))
      (Var "x" NONE) (Lit (IntLit 4))))``
val [Number i] = run_exp e14
val SOME 0 = intML.toInt i;
val e15 = ``
Let NONE "x" NONE (Lit (Bool T))
(App Equality
  (Mat (Var "x" NONE)
    [(Plit (Bool F), (Lit (IntLit 1)));
     (Pvar "y" NONE, (Var "y" NONE))])
  (Var "x" NONE))``

  val _ = print(print_Cexp 0 (exp_to_Cexp (etC (snd inits)) (term_to_exp e15)))

val (m,[v]) = mst_run_exp e15
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e16 = ``App Equality (Let NONE "x" NONE (Lit (Bool T)) (Var "x" NONE)) (Lit (Bool F))``
val (m,[v]) = mst_run_exp e16
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e17 = ``App Equality
  (Let NONE "f" NONE (Fun "_" NONE (Lit (Bool T))) (App Opapp (Var "f" NONE) (Lit (Bool T))))
  (Lit (Bool F))``
val (m,[v]) = mst_run_exp e17
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e18 = ``
Let NONE "x" NONE (Lit (Bool T))
  (App Equality
    (Let NONE "f" NONE (Fun "_" NONE (Var "x" NONE)) (App Opapp (Var "f" NONE) (Var "x" NONE)))
    (Var "x" NONE))``
val (m,[v]) = mst_run_exp e18
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e19 = ``
Let NONE "x" NONE (Lit (Bool T))
  (App Opapp (Fun "_" NONE (Var "x" NONE)) (Lit (Bool F)))``
val (m,[v]) = mst_run_exp e19
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e20 = ``
Let NONE "f" NONE (Fun "_" NONE (Lit (Bool T)))
(App Equality
  (App Opapp (Var "f" NONE) (Lit (Bool T)))
  (Lit (Bool F)))``
val (m,[v]) = mst_run_exp e20
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e21 = ``Let NONE "x" NONE (Lit (Bool T))
(App Equality
  (Let NONE "f" NONE (Fun "_" NONE (Var "x" NONE))
    (App Opapp (Var "f" NONE) (Var "x" NONE)))
  (Var "x" NONE))``
val (m,[v]) = mst_run_exp e21
val true = (OLit (Bool true)) = (bv_to_ov m v);
val listd = ``
Dtype
  [(["'a"],"list",
    [("Cons",[Tvar "'a"; Tapp [Tvar "'a"] (TC_name "list")]); ("Nil",[])])]
``
val e22 = ``Con "Cons" [Lit (Bool T); Con "Nil" []]``
val (m,[Block (t1,[v,Block (t2,[])])]) = mst_run_decs_exp ([listd],e22)
val true = valOf(numML.toInt t1) > 2;
val true = valOf(numML.toInt t2) > valOf(numML.toInt t1);
val true = (OLit (Bool true)) = (bv_to_ov m v);
val e23 = ``Mat (Con "Cons" [Lit (IntLit 2);
                 Con "Cons" [Lit (IntLit 3);
                 Con "Nil" []]])
            [(Pcon "Cons" [Pvar "x" NONE; Pvar "xs" NONE],
              Var "x" NONE);
             (Pcon "Nil" [],
              Lit (IntLit 1))]``
val [Number i] = run_decs_exp ([listd],e23)
val SOME 2 = intML.toInt i;
val e24 = ``Mat (Con "Nil" [])
            [(Pcon "Nil" [], Lit (Bool F))]``
val (m,[v]) = mst_run_decs_exp([listd],e24)
val true = (OLit (Bool false)) = (bv_to_ov m v);
val e25 = ``Mat (Con "Cons" [Lit (IntLit 2);
                 Con "Nil" []])
            [(Pcon "Cons" [Pvar "x" NONE; Pvar "xs" NONE],
              Var "x" NONE)]``
val [Number i] = run_decs_exp([listd],e25)
val SOME 2 = intML.toInt i;
val e26 = ``Mat (Con "Cons" [Lit (IntLit 2);
                 Con "Nil" []])
            [(Pcon "Cons" [Plit (IntLit 2);
              Pcon "Nil" []],
              Lit (IntLit 5))]``
val [Number i] = run_decs_exp([listd],e26)
val SOME 5 = intML.toInt i;
(*
val e27 =
CLetfun(false,["1"],[([],sumML.INL (CRaise Bind_error))],
CIf(CPrim2(CEq,CLit (IntLit i0),CLit (IntLit i0)),
    CLit (IntLit i1),
    CCall (CVar "1",[])))
val (bs,rs) = inits
val rs = compile_Cexp rs NONE e27
val bs = add_code rs bs
val bs = bc_eval bs
val [Number i] = bc_state_stack bs
val SOME 1 = intML.toInt i;
*)
val e28 = ``
Letrec NONE [("fac",NONE,("n",NONE,
  If (App Equality (Var "n" NONE) (Lit (IntLit 0)))
     (Lit (IntLit 1))
     (App (Opn Times)
       (Var "n" NONE)
       (App Opapp (Var "fac" NONE) (App (Opn Minus)
                                   (Var "n" NONE)
                                   (Lit (IntLit 1)))))))]
  (App Opapp (Var "fac" NONE) (Lit (IntLit 5)))``
val [Number i] = run_exp e28
val SOME 120 = intML.toInt i;
val d = ``Dlet NONE (Pvar "Foo" NONE) (Lit (IntLit 42))``
val e41 = ``Var "Foo" NONE``
val [Number i,Number j] = run_decs_exp([d],e41)
val SOME 42 = intML.toInt i;
val true = i = j;
val d = ``Dletrec NONE [("I",NONE,"x",NONE,(Var "x" NONE))]``
val e42 = ``App Opapp (Var "I" NONE) (Lit (IntLit 42))``
val [Number i,cl] = run_decs_exp([d],e42)
val SOME 42 = intML.toInt i;
val d0 = ``
Dletrec NONE
  [("N",NONE,"v1",NONE,
    If (App (Opb Gt) (Var "v1" NONE) (Lit (IntLit 100)))
      (App (Opn Minus) (Var "v1" NONE) (Lit (IntLit 10)))
      (App Opapp (Var "N" NONE)
         (App Opapp (Var "N" NONE)
            (App (Opn Plus) (Var "v1" NONE) (Lit (IntLit 11))))))]
``
val e29 = ``App Opapp (Var "N" NONE) (Lit (IntLit 42))``
val [Number i,cl] = run_decs_exp([d0],e29)
val SOME 91 = intML.toInt i;
val e35 = ``Let NONE "f" NONE (Fun "x" NONE (Fun "y" NONE (App (Opn Plus) (Var "x" NONE) (Var "y" NONE)))) (App Opapp (App Opapp (Var "f" NONE) (Lit (IntLit 2))) (Lit (IntLit 3)))``
val [Number i] = run_exp e35
val SOME 5 = intML.toInt i;
val e36 = ``Letrec NONE [("f", NONE, ("x", NONE, (Fun "y" NONE (App (Opn Plus) (Var "x" NONE) (Var "y" NONE)))))] (App Opapp (App Opapp (Var "f" NONE) (Lit (IntLit 2))) (Lit (IntLit 3)))``
val [Number i] = run_exp e36
val SOME 5 = intML.toInt i;
val e37 = ``Letrec NONE [("z", NONE, ("x", NONE, (Mat (Var "x" NONE) [(Plit (IntLit 0), (Var "x" NONE));(Pvar "y" NONE, App Opapp (Var "z" NONE) (App (Opn Minus) (Var "x" NONE) (Var "y" NONE)))])))] (App Opapp (Var "z" NONE) (Lit (IntLit 5)))``
val [Number i] = run_exp e37
val SOME 0 = intML.toInt i;
val e38 = ``Let NONE "z" NONE (Fun "x" NONE (Mat (Var "x" NONE) [(Plit (IntLit 0), (Var "x" NONE));(Pvar "y" NONE, (App (Opn Minus) (Var "x" NONE) (Var "y" NONE)))])) (App Opapp (Var "z" NONE) (Lit (IntLit 5)))``
val [Number i] = run_exp e38
val SOME 0 = intML.toInt i;
val e39 = ``Letrec NONE [("z", NONE, ("x", NONE, (Mat (Var "x" NONE) [(Plit (IntLit 0), (Var "x" NONE));(Pvar "y" NONE, (App (Opn Minus) (Var "x" NONE) (Var "y" NONE)))])))] (App Opapp (Var "z" NONE) (Lit (IntLit 5)))``
val [Number i] = run_exp e39
val SOME 0 = intML.toInt i;
val paird = ``
Dtype [(["'a"; "'b"],"prod",[("Pair_type",[Tvar "'a"; Tvar "'b"])])]
``
val _ = reset_translation()
val _ = translate listTheory.APPEND
val _ = finalise_translation()
val ds = dest_list I (get_decls())
val e33 = ``App Opapp (Var "APPEND" NONE) (Con "Nil" [])``
val (m,st) = mst_run_decs_exp (ds,e33)
val tm = bv_to_ov m (hd st)
val true = tm = OFn;
val e34 = ``App Opapp (App Opapp (Var "APPEND" NONE) (Con "Nil" []))
                      (Con "Nil" [])``
val (m,st) = mst_run_decs_exp (ds,e34)
val [r,cl] = st
val tm = bv_to_ov m r
val true = tm = OConv ("Nil",[])
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
val true = tm = OConv ("Cons",[OLit (IntLit (intML.fromInt 4)), OConv ("Nil",[])]);
val _ = reset_translation()
val _ = translate sortingTheory.PART_DEF
val _ = translate sortingTheory.PARTITION_DEF
val _ = translate listTheory.APPEND
val _ = translate sortingTheory.QSORT_DEF
val _ = finalise_translation()
val ds = dest_list I (get_decls())
val t = hol2deep ``QSORT (λx y. x ≤ y) [9;8;7;6;2;3;4;5:num]``
val e31 = h t;
val (m,st) = mst_run_decs_exp (ds,e31)
val [res,clQSORT,clPARTITION,clPART,clAPPEND] = st
val tm = bv_to_ov m res
val true = tm = term_to_ov(hol2val ``[2;3;4;5;6;7;8;9:num]``);
val d = ``
Dlet NONE (Pvar "add1" NONE)
  (Fun "x" NONE (App (Opn Plus) (Var "x" NONE) (Lit (IntLit 1))))``
val e40 = ``App Opapp (Var "add1" NONE) (Lit (IntLit 1))``
val (m,st) = mst_run_decs_exp ([d],e40)
val [res,add1] = st
val true = bv_to_ov m res = term_to_ov(hol2val ``2:int``);
val e43 = ``Letrec NONE [("o",NONE,"n",NONE,
  If (App Equality (Var "n" NONE) (Lit (IntLit 0)))
     (Var "n" NONE)
     (App Opapp
       (Var "o" NONE)
       (App (Opn Minus) (Var "n" NONE) (Lit (IntLit 1)))))]
  (App Opapp (Var "o" NONE) (Lit (IntLit 1000)))``
val (bs43,_) = prep_exp inits e43
val SOME s43 = bc_eval_limit 12 bs43
val [Number i] = bc_state_stack s43
val SOME 0 = intML.toInt i;
val d = ``Dletrec NONE
[("o",NONE,"n",NONE,
  If (App Equality (Var "n" NONE) (Lit (IntLit 0)))
     (Var "n" NONE)
     (App Opapp
       (Var "o" NONE)
       (App (Opn Minus) (Var "n" NONE) (Lit (IntLit 1)))))]``
val e44 = ``App Opapp (Var "o" NONE) (Lit (IntLit 1000))``
val [Number i, cl] = run_decs_exp ([d],e44)
val SOME 0 = intML.toInt i;
val d0 = paird
val d1 = ``Dlet NONE (Pcon "Pair_type" [Pvar "x" NONE;Pvar "y" NONE]) (Con "Pair_type" [Lit (IntLit 1);Lit (IntLit 2)])``
val d2 = ``Dlet NONE (Pvar "x" NONE) (Lit (IntLit 3))``
val e45 = ``Con "Pair_type" [Var "x" NONE;Var "y" NONE]``
val [Block (_,[Number xb,Number yb]),Number y,Number x] = run_decs_exp ([d0,d1,d2],e45)
val SOME 3 = intML.toInt x
val SOME 2 = intML.toInt y
val true = xb = x
val true = yb = y;
val d1 = ``Dlet NONE (Pcon "Pair_type" [Pvar "y" NONE;Pvar "x" NONE]) (Con "Pair_type" [Lit (IntLit 1);Lit (IntLit 2)])``
val d2 = ``Dlet NONE (Pvar "x" NONE) (Lit (IntLit 3))``
val e46 = ``Con "Pair_type" [Var "x" NONE;Var "y" NONE]``
val [Block (_,[Number xb,Number yb]),Number x,Number y] = run_decs_exp ([d0,d1,d2],e46)
val SOME 3 = intML.toInt xb
val SOME 1 = intML.toInt yb
val true = x = xb
val true = y = yb;
val d0 = paird
val d1 = ``Dlet NONE (Pcon "Pair_type" [Pvar "x" NONE;Pvar "y" NONE]) (Con "Pair_type" [Lit (IntLit 1);Lit (IntLit 2)])``
val d2 = ``Dlet NONE (Pvar "x" NONE) (Lit (IntLit 3))``
val d3 = ``Dlet NONE (Pvar "y" NONE) (Lit (IntLit 4))``
val e47 = ``Con "Pair_type" [
              Con "Pair_type" [Var "x" NONE; Var "y" NONE];
              Let NONE "x" NONE (Fun "x" NONE (App (Opn Plus) (Var "x" NONE) (Var "y" NONE)))
                (App Opapp (Var "x" NONE) (Var "y" NONE))]``
val [Block (_,[Block (_,[Number x3,Number y4]),Number yy]),Number y,Number x] = run_decs_exp([d0,d1,d2,d3],e47)
val SOME 4 = intML.toInt y
val SOME 3 = intML.toInt x
val SOME 3 = intML.toInt x3
val SOME 4 = intML.toInt y4
val SOME 8 = intML.toInt yy;
val d0 = ``Dlet NONE (Pvar "x" NONE) (Let NONE "x" NONE (Lit (IntLit 1)) (App (Opn Minus) (Var "x" NONE) (Var "x" NONE)))``
val e48 = ``Var "x" NONE``
val [Number xv,Number xd] = run_decs_exp([d0],e48)
val SOME 0 = intML.toInt xv
val SOME 0 = intML.toInt xd;
val d0 = ``Dlet NONE (Pvar "x" NONE) (Let NONE "x" NONE (Lit (IntLit 1)) (App (Opn Minus) (Var "x" NONE) (Var "x" NONE)))``
val d1 = ``Dlet NONE (Pvar "x" NONE) (App (Opn Minus) (Var "x" NONE) (Let NONE "x" NONE (Lit (IntLit 1)) (Var "x" NONE)))``
val e49 = ``App (Opn Times) (Var "x" NONE) (Let NONE "x" NONE (Lit (IntLit (-1))) (Var "x" NONE))``
val [Number r,Number x] = run_decs_exp([d0,d1],e49)
val SOME ~1 = intML.toInt x
val SOME 1 = intML.toInt r;
val d0 = paird
val d1 = ``Dlet NONE (Pcon "Pair_type" [Pvar "y" NONE;Pvar "x" NONE]) (Con "Pair_type" [Lit (IntLit 1);Lit (IntLit 2)])``
val e50 = ``Var "y" NONE``
val [Number r, Number x, Number y] = run_decs_exp([d0,d1],e50)
val SOME 2 = intML.toInt x
val SOME 1 = intML.toInt y
val true = r = y;
val d0 = ``Dlet NONE (Pvar "x" NONE) (Lit (IntLit 1))``
val d1 = ``Dtype [([],"unit",[("()",[])])]``
val d2 = ``Dlet NONE (Pvar "f" NONE) (Fun " " NONE (Mat (Var " " NONE) [(Pcon "()" [],App (Opn Plus) (Var "x" NONE) (Lit (IntLit 1)))]))``
val d3 = ``Dlet NONE (Pvar "x" NONE) (Lit (IntLit 100))``
val e51 = ``App Opapp (Var "f" NONE) (Con "()" [])``
val [Number r, _, Number x] = run_decs_exp([d0,d1,d2,d3],e51)
val SOME 2 = intML.toInt r
val SOME 100 = intML.toInt x;
val d0 = paird
val e52 = ``Let NONE "x" NONE (Con "Pair_type" [Lit (IntLit 1);Lit (IntLit 2)])
  (Mat (Var "x" NONE)
      [(Pcon "Pair_type" [Pvar "x" NONE;Plit (IntLit 2)], Lit (IntLit 1))])``
val [Number r] = run_decs_exp([d0],e52)
val SOME 1 = intML.toInt r;
val d0 = paird
val e53 = ``Let NONE "x" NONE (Con "Pair_type" [Lit (IntLit 1);Con "Pair_type" [Lit (IntLit 2); Lit (IntLit 3)]])
  (Mat (Var "x" NONE)
      [(Pcon "Pair_type" [Pvar "x" NONE;Pcon "Pair_type" [Pvar "y" NONE;Pvar "z" NONE]], Var "y" NONE)])``
val [Number r] = run_decs_exp([d0],e53)
val SOME 2 = intML.toInt r;
val e54 = ``Letrec NONE [
  ("x",NONE,"x",NONE,App (Opn Plus) (Var "x" NONE) (Lit (IntLit 1)));
  ("f",NONE,"y",NONE,App Opapp (Var "x" NONE) (Var "y" NONE))]
    (App Opapp (Var "f" NONE) (Lit (IntLit 1)))``
val [Number r] = run_exp e54
val SOME 2 = intML.toInt r;
val e55 = ``Letrec NONE [
  ("f",NONE,"y",NONE,App Opapp (Var "x" NONE) (Var "y" NONE));
  ("x",NONE,"x",NONE,App (Opn Plus) (Var "x" NONE) (Lit (IntLit 1)))]
    (App Opapp (Var "f" NONE) (Lit (IntLit 1)))``
val [Number r] = run_exp e55
val SOME 2 = intML.toInt r;
val e56 = ``Letrec NONE [
  ("x",NONE,"x",NONE,App (Opn Plus) (Var "x" NONE) (Lit (IntLit 1)))]
    (App Opapp (Var "x" NONE) (Lit (IntLit 1)))``
val [Number r] = run_exp e56
val SOME 2 = intML.toInt r;
val e57 = ``Letrec NONE [
  ("f",NONE,"y",NONE,App Opapp (Var "g" NONE) (Var "y" NONE));
  ("g",NONE,"x",NONE,App (Opn Plus) (Var "x" NONE) (Lit (IntLit 1)))]
    (App Opapp (Var "f" NONE) (Lit (IntLit 1)))``
val [Number r] = run_exp e57
val SOME 2 = intML.toInt r;
val e58 = ``Letrec NONE [
  ("g",NONE,"x",NONE,App (Opn Plus) (Var "x" NONE) (Lit (IntLit 1)));
  ("f",NONE,"y",NONE,App Opapp (Var "g" NONE) (Var "y" NONE))]
    (App Opapp (Var "f" NONE) (Lit (IntLit 1)))``
val [Number r] = run_exp e58
val SOME 2 = intML.toInt r;
val e59 = ``Let NONE "x" NONE (Lit (IntLit 2))
  (Letrec NONE [
    ("x",NONE,"x",NONE,App (Opn Plus) (Var "x" NONE) (Lit (IntLit 1)));
    ("f",NONE,"y",NONE,App Opapp (Var "x" NONE) (Var "y" NONE))]
      (App Opapp (Var "f" NONE) (Lit (IntLit 1))))``
val [Number r] = run_exp e59
val SOME 2 = intML.toInt r;
val e60 = ``Let NONE "i" NONE (Lit (IntLit 10))
  (Let NONE "1" NONE (Lit (IntLit 1))
    (Letrec NONE [
("z",NONE,"j",NONE,App Equality (Var "j" NONE) (Lit (IntLit 0)));
("f0",NONE,"i",NONE,If (App Opapp (Var "z" NONE) (Var "i" NONE)) (Lit (Bool T))
         (App Opapp (Var "f2" NONE) (App Opapp (Var "s" NONE) (Var "i" NONE))));
("f1",NONE,"i",NONE,If (App Opapp (Var "z" NONE) (Var "i" NONE)) (Lit (Bool F))
         (App Opapp (Var "f0" NONE) (App Opapp (Var "s" NONE) (Var "i" NONE))));
("f2",NONE,"i",NONE,If (App Opapp (Var "z" NONE) (Var "i" NONE)) (Lit (Bool F))
         (App Opapp (Var "f1" NONE) (App Opapp (Var "s" NONE) (Var "i" NONE))));
("s",NONE,"k",NONE,App (Opn Minus) (Var "k" NONE) (Var "1" NONE))]
  (App Opapp (Var "f0" NONE) (Var "i" NONE))))``
val (m,[r]) = mst_run_exp e60
val true = (OLit (Bool false)) = bv_to_ov m r;
val d0 = ``Dlet NONE (Pvar "1" NONE) (Lit (IntLit 1))``
val d1 = ``Dletrec NONE [
("z",NONE,"j",NONE,App Equality (Var "j" NONE) (Lit (IntLit 0)));
("f0",NONE,"i",NONE,If (App Opapp (Var "z" NONE) (Var "i" NONE)) (Lit (Bool T))
         (App Opapp (Var "f2" NONE) (App Opapp (Var "s" NONE) (Var "i" NONE))));
("f1",NONE,"i",NONE,If (App Opapp (Var "z" NONE) (Var "i" NONE)) (Lit (Bool F))
         (App Opapp (Var "f0" NONE) (App Opapp (Var "s" NONE) (Var "i" NONE))));
("f2",NONE,"i",NONE,If (App Opapp (Var "z" NONE) (Var "i" NONE)) (Lit (Bool F))
         (App Opapp (Var "f1" NONE) (App Opapp (Var "s" NONE) (Var "i" NONE))));
("s",NONE,"k",NONE,App (Opn Minus) (Var "k" NONE) (Var "1" NONE))]``
val e61 = ``App Opapp (Var "f0" NONE) (Lit (IntLit 12))``
val (m,[r,_,_,_,_,_,_]) = mst_run_decs_exp([d0,d1],e61)
val true = (OLit (Bool true)) = bv_to_ov m r;
val e62 = ``Letrec NONE ["f",NONE,"x",NONE,Var "x" NONE] (App Opapp (Var "f" NONE) (Lit (IntLit 42)))``
val [Number r] = run_exp e62
val SOME 42 = intML.toInt r;
val e63 = ``Letrec NONE [("f",NONE,"x",NONE,App Opapp (Var "g" NONE) (Var "x" NONE));
                    ("g",NONE,"x",NONE,Var "x" NONE)]
                    (App Opapp (Var "f" NONE) (Lit (IntLit 42)))``
val [Number r] = run_exp e63
val SOME 42 = intML.toInt r;
val d0 = ``Dlet NONE (Pvar "1" NONE) (Lit (IntLit 1))``
val d1 = ``Dletrec NONE [
("a",NONE,"b",NONE,App Equality (Var "b" NONE) (Lit (IntLit 0)));
("c",NONE,"d",NONE,If (App Opapp (Var "a" NONE) (Var "d" NONE)) (Lit (Bool T))
              (App Opapp (Var "g" NONE) (App Opapp (Var "i" NONE) (Var "d" NONE))));
("e",NONE,"f",NONE,If (App Opapp (Var "a" NONE) (Var "f" NONE)) (Lit (Bool F))
              (App Opapp (Var "c" NONE) (App Opapp (Var "i" NONE) (Var "f" NONE))));
("g",NONE,"h",NONE,If (App Opapp (Var "a" NONE) (Var "h" NONE)) (Lit (Bool F))
              (App Opapp (Var "e" NONE) (App Opapp (Var "i" NONE) (Var "h" NONE))));
("i",NONE,"j",NONE,App (Opn Minus) (Var "j" NONE) (Var "1" NONE))]``
val e64 = ``App Opapp (Var "c" NONE) (Lit (IntLit 12))``
val (m,[r,_,_,_,_,_,_]) = mst_run_decs_exp([d0,d1],e64)
val true = (OLit (Bool true)) = bv_to_ov m r;
val d1 = ``Dletrec NONE [
("a",NONE,"b",NONE,App Equality (Var "b" NONE) (Lit (IntLit 0)));
("c",NONE,"d",NONE,If (App Opapp (Var "a" NONE) (Var "d" NONE)) (Lit (Bool T))
         (App Opapp (Var "g" NONE) (App Opapp (Var "i" NONE) (Var "d" NONE))));
("e",NONE,"f",NONE,If (App Opapp (Var "a" NONE) (Var "f" NONE)) (Lit (Bool F))
         (App Opapp (Var "c" NONE) (App Opapp (Var "i" NONE) (Var "f" NONE))));
("g",NONE,"h",NONE,If (App Opapp (Var "a" NONE) (Var "h" NONE)) (Lit (Bool F))
         (App Opapp (Var "e" NONE) (App Opapp (Var "i" NONE) (Var "h" NONE))));
("i",NONE,"j",NONE,App (Opn Minus) (Var "j" NONE) (Lit (IntLit 1)))]``
val e65 = ``App Opapp (Var "c" NONE) (Lit (IntLit 12))``
val (m,[r,_,_,_,_,_]) = mst_run_decs_exp([d1],e65)
val true = (OLit (Bool true)) = bv_to_ov m r;
val e66 = ``Letrec NONE [
("a",NONE,"b",NONE,App Equality (Var "b" NONE) (Lit (IntLit 0)));
("c",NONE,"d",NONE,If (App Opapp (Var "a" NONE) (Var "d" NONE)) (Lit (Bool T))
         (App Opapp (Var "g" NONE) (App Opapp (Var "i" NONE) (Var "d" NONE))));
("e",NONE,"f",NONE,If (App Opapp (Var "a" NONE) (Var "f" NONE)) (Lit (Bool F))
         (App Opapp (Var "c" NONE) (App Opapp (Var "i" NONE) (Var "f" NONE))));
("g",NONE,"h",NONE,If (App Opapp (Var "a" NONE) (Var "h" NONE)) (Lit (Bool F))
         (App Opapp (Var "e" NONE) (App Opapp (Var "i" NONE) (Var "h" NONE))));
("i",NONE,"j",NONE,App (Opn Minus) (Var "j" NONE) (Lit (IntLit 1)))]
(App Opapp (Var "c" NONE) (Lit (IntLit 12)))``
val (m,[r]) = mst_run_exp e66
val true = (OLit (Bool true)) = bv_to_ov m r;
val e67 = ``Let NONE "x" NONE (Lit (Bool T)) (If (Var "x" NONE) (Lit (IntLit 1)) (Lit (IntLit 2)))``
val (m,[r]) = mst_run_exp e67
val true = (OLit (IntLit (intML.fromInt 1))) = bv_to_ov m r;
val e68 = ``Letrec NONE [
  ("not",NONE,"x",NONE,Mat (Var "x" NONE)
               [(Plit (Bool T),Lit(Bool F));
                (Plit (Bool F),Lit(Bool T))])]
   (If (Let NONE "x" NONE (Lit (Bool T)) (App Opapp (Var "not" NONE) (Var "x" NONE))) (Lit (IntLit 1)) (Lit (IntLit 2)))``
val (m,[r]) = mst_run_exp e68
val true = (OLit (IntLit (intML.fromInt 2))) = bv_to_ov m r;
val e69 = ``Let NONE "f" NONE
  (Fun "x" NONE
    (If (Lit (Bool F))
        (Let NONE "y" NONE (Lit (IntLit 1))
          (Var "y" NONE))
        (App Opapp (Fun "z" NONE (Var "z" NONE)) (Lit (IntLit 2)))))
  (App Opapp (Var "f" NONE) (Lit (IntLit 0)))``
val (m,[r]) = mst_run_exp e69
val true = (OLit (IntLit (intML.fromInt 2))) = bv_to_ov m r;
val e70 = ``Let NONE "f" NONE
  (Fun "x" NONE
    (If (Lit (Bool F))
        (Lit (IntLit 1))
        (App Opapp (Fun "z" NONE (Var "z" NONE)) (Lit (IntLit 2)))))
  (App Opapp (Var "f" NONE) (Lit (IntLit 0)))``
val (m,[r]) = mst_run_exp e70
val true = (OLit (IntLit (intML.fromInt 2))) = bv_to_ov m r;
