(*
  Basic tests and readiness challenges for source_lift_consts, based on plan.txt.

  These are specifications, not snapshots of current compiler output.
  Some intentionally require behaviour the pass does not yet implement.
  In particular, named closed/closed-ish helpers must move to declarations,
  curried functions must stay whole, and all binders must reserve fresh names.

  Local helper names in the plan examples are retained. Anonymous lifted
  constants use the pass's constant_ / appended-underscore convention.
  Hygiene examples reserve the full binder spelling using the existing
  length-plus-one convention, including binders with no source occurrence.

  Each expected result is an explicit AST. There are no cheats, conditional
  tests, computed expected results, or changes to the compiler in this file.
*)
Theory source_lift_consts_test[no_sig_docs]
Ancestors
  source_lift_consts evaluate
Libs
  preamble

(* Ground free-variable maps need these computation equations for EVAL_TAC. *)
val _ = computeLib.add_funs
  [finite_mapTheory.FUNION_FEMPTY_1, finite_mapTheory.FUNION_FUPDATE_1,
   finite_mapTheory.DRESTRICT_FEMPTY, finite_mapTheory.DRESTRICT_FUPDATE,
   finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_FUNION,
   finite_mapTheory.NOT_EQ_FEMPTY_FUPDATE,
   pred_setTheory.IN_COMPL, pred_setTheory.IN_SING];

Overload comp[local] = ``source_lift_consts$compile_dec``

(*
  Small integers, characters, bytes, unit and nullary constructors stay inline, even
  two functions deep.
*)
Theorem test_cheap_leaves_stay_in_nested_functions[local]:
  comp
    (Dlet NoLocs (Pvar «cheap»)
      (Fun «n»
        (Fun «m»
          (Con NONE
            [
              (Var (Short «n»));
              (Lit (IntLit 0));
              (Lit (IntLit (-17)));
              (Lit (Char #"x"));
              (Lit (Word8 255w));
              (Con NONE []);
              (Con (SOME (Short «None»)) [])]))))
  =
    (Dlet NoLocs (Pvar «cheap»)
      (Fun «n»
        (Fun «m»
          (Con NONE
            [
              (Var (Short «n»));
              (Lit (IntLit 0));
              (Lit (IntLit (-17)));
              (Lit (Char #"x"));
              (Lit (Word8 255w));
              (Con NONE []);
              (Con (SOME (Short «None»)) [])]))))
Proof
  EVAL_TAC
QED

(*
  Lift the whole nested constant payload once, rather than allocating separate
  bindings for its constant children.
*)
Theorem test_maximal_constant_constructor[local]:
  comp
    (Dlet NoLocs (Pvar «payload»)
      (Fun «n»
        (Fun «m»
          (Con NONE
            [
              (Lit (StrLit «a rather expensive constant»));
              (Con NONE
                [
                  (Lit (IntLit 1208925819614629174706176));
                  (Lit (IntLit (-1208925819614629174706176)));
                  (Con (SOME (Short «None»)) [])])]))))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_»)
          (Con NONE
            [
              (Lit (StrLit «a rather expensive constant»));
              (Con NONE
                [
                  (Lit (IntLit 1208925819614629174706176));
                  (Lit (IntLit (-1208925819614629174706176)));
                  (Con (SOME (Short «None»)) [])])]))]
      [
        (Dlet NoLocs (Pvar «payload»)
          (Fun «n» (Fun «m» (Var (Short «constant_»)))))])
Proof
  EVAL_TAC
QED

(*
  A nonconstant outer tuple must still expose independent expensive constant
  children in left-to-right order.
*)
Theorem test_mixed_constructor_siblings[local]:
  comp
    (Dlet NoLocs (Pvar «siblings»)
      (Fun «n»
        (Con NONE
          [
            (Var (Short «n»));
            (Con NONE
              [(Lit (StrLit «positive»)); (Lit (IntLit 1208925819614629174706176))]);
            (Con NONE
              [(Lit (StrLit «negative»)); (Lit (IntLit (-1208925819614629174706176)))])])))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_»)
          (Con NONE
            [(Lit (StrLit «positive»)); (Lit (IntLit 1208925819614629174706176))]));
        (Dlet NoLocs (Pvar «constant__»)
          (Con NONE
            [(Lit (StrLit «negative»)); (Lit (IntLit (-1208925819614629174706176)))]))]
      [
        (Dlet NoLocs (Pvar «siblings»)
          (Fun «n»
            (Con NONE
              [(Var (Short «n»)); (Var (Short «constant_»)); (Var (Short «constant__»))])))])
Proof
  EVAL_TAC
QED

(*
  Both branches are visited inside a curried function; their two maximal payloads
  get distinct names.
*)
Theorem test_constants_in_both_nested_branches[local]:
  comp
    (Dlet NoLocs (Pvar «choose»)
      (Fun «flag»
        (Fun «unused»
          (If (Var (Short «flag»))
            (Con NONE
              [(Lit (StrLit «yes»)); (Lit (IntLit 1208925819614629174706176))])
            (Con NONE
              [(Lit (StrLit «no»)); (Lit (IntLit (-1208925819614629174706176)))])))))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_»)
          (Con NONE
            [(Lit (StrLit «yes»)); (Lit (IntLit 1208925819614629174706176))]));
        (Dlet NoLocs (Pvar «constant__»)
          (Con NONE
            [(Lit (StrLit «no»)); (Lit (IntLit (-1208925819614629174706176)))]))]
      [
        (Dlet NoLocs (Pvar «choose»)
          (Fun «flag»
            (Fun «unused»
              (If (Var (Short «flag»)) (Var (Short «constant_»)) (Var (Short «constant__»))))))])
Proof
  EVAL_TAC
QED

(*
  Constants outside function bodies do not acquire another declaration-level
  binding.
*)
Theorem test_top_level_expensive_data_stays_put[local]:
  comp
    (Dlet NoLocs (Pvar «top»)
      (Let (SOME «payload»)
        (Con NONE
          [(Lit (StrLit «top level»)); (Lit (IntLit 1208925819614629174706176))])
        (Con NONE [(Var (Short «payload»)); (Lit (IntLit 1))])))
  =
    (Dlet NoLocs (Pvar «top»)
      (Let (SOME «payload»)
        (Con NONE
          [(Lit (StrLit «top level»)); (Lit (IntLit 1208925819614629174706176))])
        (Con NONE [(Var (Short «payload»)); (Lit (IntLit 1))])))
Proof
  EVAL_TAC
QED

(*
  fun foo y = (y, fn x => [fn y => "hi"]). The inner y shadows foo's
  parameter. The list separates the lambdas, so lift the string, inner
  closure, singleton list and outer closure in dependency order.
*)
Theorem test_nested_function_list_dependency_chain[local]:
  comp
    (Dletrec NoLocs
      [(«foo», «y»,
        Con NONE
          [Var (Short «y»);
           Fun «x»
             (Con (SOME (Short «::»))
               [Fun «y» (Lit (StrLit «hi»));
                Con (SOME (Short «[]»)) []])])])
  =
    (Dlocal
      [
        Dlet NoLocs (Pvar «constant_»)
          (Lit (StrLit «hi»));
        Dlet NoLocs (Pvar «constant__»)
          (Fun «y» (Var (Short «constant_»)));
        Dlet NoLocs (Pvar «constant___»)
          (Con (SOME (Short «::»))
            [Var (Short «constant__»);
             Con (SOME (Short «[]»)) []]);
        Dlet NoLocs (Pvar «constant____»)
          (Fun «x» (Var (Short «constant___»)))
      ]
      [
        Dletrec NoLocs
          [(«foo», «y»,
            Con NONE [Var (Short «y»); Var (Short «constant____»)])]
      ])
Proof
  EVAL_TAC
QED

(*
  An anonymous two-argument function is lifted as one closure, leaving consecutive
  Fun nodes intact for multi-argument optimisation.
*)
Theorem test_closed_curried_function_stays_whole[local]:
  comp
    (Dlet NoLocs (Pvar «invoke»)
      (Fun «n»
        (App Opapp
          [(Fun «x» (Fun «y» (Var (Short «y»)))); (Var (Short «n»))])))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_»)
          (Fun «x» (Fun «y» (Var (Short «y»)))))]
      [
        (Dlet NoLocs (Pvar «invoke»)
          (Fun «n»
            (App Opapp [(Var (Short «constant_»)); (Var (Short «n»))])))])
Proof
  EVAL_TAC
QED

(*
  An anonymous two-argument function is lifted as one closure, leaving consecutive
  Fun nodes intact for multi-argument optimisation.
*)
Theorem test_curried_function_capturing_first_argument[local]:
  comp
    (Dlet NoLocs (Pvar «invoke»)
      (Fun «n»
        (App Opapp
          [
            (Fun «x»
              (Fun «y»
                (App (Arith Add IntT) [(Var (Short «x»)); (Var (Short «y»))])));
            (Var (Short «n»))])))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_»)
          (Fun «x»
            (Fun «y»
              (App (Arith Add IntT) [(Var (Short «x»)); (Var (Short «y»))]))))]
      [
        (Dlet NoLocs (Pvar «invoke»)
          (Fun «n»
            (App Opapp [(Var (Short «constant_»)); (Var (Short «n»))])))])
Proof
  EVAL_TAC
QED

(*
  The inner function captures the enclosing argument, even beneath two additional
  Fun nodes.
*)
Theorem test_outer_capture_prevents_whole_closure_lift[local]:
  comp
    (Dlet NoLocs (Pvar «capture»)
      (Fun «n»
        (App Opapp
          [
            (Fun «x»
              (Fun «y»
                (Con NONE
                  [(Var (Short «n»)); (Var (Short «x»)); (Var (Short «y»))])));
            (Var (Short «n»))])))
  =
    (Dlet NoLocs (Pvar «capture»)
      (Fun «n»
        (App Opapp
          [
            (Fun «x»
              (Fun «y»
                (Con NONE
                  [(Var (Short «n»)); (Var (Short «x»)); (Var (Short «y»))])));
            (Var (Short «n»))])))
Proof
  EVAL_TAC
QED

(* A closure that must remain local still contains an independently liftable string. *)
Theorem test_lift_data_inside_capturing_closure[local]:
  comp
    (Dlet NoLocs (Pvar «capture_data»)
      (Fun «n»
        (App Opapp
          [
            (Fun «x»
              (Con NONE
                [
                  (Var (Short «n»));
                  (Var (Short «x»));
                  (Lit (StrLit «captured function payload»))]));
            (Var (Short «n»))])))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_») (Lit (StrLit «captured function payload»)))]
      [
        (Dlet NoLocs (Pvar «capture_data»)
          (Fun «n»
            (App Opapp
              [
                (Fun «x»
                  (Con NONE
                    [(Var (Short «n»)); (Var (Short «x»)); (Var (Short «constant_»))]));
                (Var (Short «n»))])))])
Proof
  EVAL_TAC
QED

(*
  The inner n shadows the outer n, so the function is closed despite using the same
  spelling.
*)
Theorem test_parameter_shadowing_makes_inner_function_closed[local]:
  comp
    (Dlet NoLocs (Pvar «shadow»)
      (Fun «n»
        (App Opapp [(Fun «n» (Var (Short «n»))); (Var (Short «n»))])))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_»)
          (Fun «n» (Var (Short «n»))))]
      [
        (Dlet NoLocs (Pvar «shadow»)
          (Fun «n»
            (App Opapp [(Var (Short «constant_»)); (Var (Short «n»))])))])
Proof
  EVAL_TAC
QED

(*
  The first plan example: move the named local function to declarations and remove
  its local Letrec wrapper.
*)
Theorem test_named_closed_function_from_plan[local]:
  comp
    (Dletrec NoLocs
      [
        («foo», «n»,
          (Letrec
            [(«bar»,«m»,(App (Arith Add IntT) [(Var (Short «m»)); (Lit (IntLit 1))]))]
            (App Opapp [(Var (Short «bar»)); (Var (Short «n»))])))])
  =
    (Dlocal
      [
        (Dletrec NoLocs
          [(«bar»,«m»,(App (Arith Add IntT) [(Var (Short «m»)); (Lit (IntLit 1))]))])]
      [
        (Dletrec NoLocs
          [(«foo»,«n»,(App Opapp [(Var (Short «bar»)); (Var (Short «n»))]))])])
Proof
  EVAL_TAC
QED

(*
  The second plan example: hoist the whole named curried value, never splitting off
  its inner Fun.
*)
Theorem test_named_curried_value_from_plan[local]:
  comp
    (Dletrec NoLocs
      [
        («foo», «n»,
          (Let (SOME «bar»)
            (Fun «x» (Fun «y» (Var (Short «y»))))
            (App Opapp
              [(App Opapp [(Var (Short «bar»)); (Var (Short «n»))]); (Lit (IntLit 5))])))])
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «bar»)
          (Fun «x» (Fun «y» (Var (Short «y»)))))]
      [
        (Dletrec NoLocs
          [
            («foo», «n»,
              (App Opapp
                [(App Opapp [(Var (Short «bar»)); (Var (Short «n»))]); (Lit (IntLit 5))]))])])
Proof
  EVAL_TAC
QED

(*
  h2 and h3 become liftable only after their earlier dependencies are hoisted;
  preserve dependency order across three Letrec layers.
*)
Theorem test_three_stage_closedish_dependency_chain[local]:
  comp
    (Dletrec NoLocs
      [
        («foo», «n»,
          (Letrec
            [(«h1»,«m»,(App (Arith Add IntT) [(Var (Short «m»)); (Lit (IntLit 1))]))]
            (Letrec
              [(«h2»,«k»,(App Opapp [(Var (Short «h1»)); (Var (Short «k»))]))]
              (Letrec
                [(«h3»,«j»,(App Opapp [(Var (Short «h2»)); (Var (Short «j»))]))]
                (App Opapp [(Var (Short «h3»)); (Var (Short «n»))])))))])
  =
    (Dlocal
      [
        (Dletrec NoLocs
          [(«h1»,«m»,(App (Arith Add IntT) [(Var (Short «m»)); (Lit (IntLit 1))]))]);
        (Dletrec NoLocs
          [(«h2»,«k»,(App Opapp [(Var (Short «h1»)); (Var (Short «k»))]))]);
        (Dletrec NoLocs
          [(«h3»,«j»,(App Opapp [(Var (Short «h2»)); (Var (Short «j»))]))])]
      [
        (Dletrec NoLocs
          [(«foo»,«n»,(App Opapp [(Var (Short «h3»)); (Var (Short «n»))]))])])
Proof
  EVAL_TAC
QED

(*
  No member of a three-stage dependency chain can escape when its root captures the
  outer parameter.
*)
Theorem test_captured_root_blocks_dependency_chain[local]:
  comp
    (Dletrec NoLocs
      [
        («foo», «n»,
          (Letrec
            [(«h1»,«m»,(App (Arith Add IntT) [(Var (Short «n»)); (Var (Short «m»))]))]
            (Letrec
              [(«h2»,«k»,(App Opapp [(Var (Short «h1»)); (Var (Short «k»))]))]
              (Letrec
                [(«h3»,«j»,(App Opapp [(Var (Short «h2»)); (Var (Short «j»))]))]
                (App Opapp [(Var (Short «h3»)); (Var (Short «n»))])))))])
  =
    (Dletrec NoLocs
      [
        («foo», «n»,
          (Letrec
            [(«h1»,«m»,(App (Arith Add IntT) [(Var (Short «n»)); (Var (Short «m»))]))]
            (Letrec
              [(«h2»,«k»,(App Opapp [(Var (Short «h1»)); (Var (Short «k»))]))]
              (Letrec
                [(«h3»,«j»,(App Opapp [(Var (Short «h2»)); (Var (Short «j»))]))]
                (App Opapp [(Var (Short «h3»)); (Var (Short «n»))])))))])
Proof
  EVAL_TAC
QED

(*
  Lift a closed mutually recursive group together; neither forward nor backward
  recursive calls are outer captures.
*)
Theorem test_closed_mutually_recursive_group[local]:
  comp
    (Dletrec NoLocs
      [
        («parity», «n»,
          (Letrec
            [
              («even», «k»,
                (If
                  (App (Test Equal IntT) [(Var (Short «k»)); (Lit (IntLit 0))])
                  (Con (SOME (Short «True»)) [])
                  (App Opapp
                    [
                      (Var (Short «odd»));
                      (App (Arith Add IntT) [(Var (Short «k»)); (Lit (IntLit (-1)))])])));
              («odd», «k»,
                (If
                  (App (Test Equal IntT) [(Var (Short «k»)); (Lit (IntLit 0))])
                  (Con (SOME (Short «False»)) [])
                  (App Opapp
                    [
                      (Var (Short «even»));
                      (App (Arith Add IntT) [(Var (Short «k»)); (Lit (IntLit (-1)))])])))]
            (App Opapp [(Var (Short «even»)); (Var (Short «n»))])))])
  =
    (Dlocal
      [
        (Dletrec NoLocs
          [
            («even», «k»,
              (If
                (App (Test Equal IntT) [(Var (Short «k»)); (Lit (IntLit 0))])
                (Con (SOME (Short «True»)) [])
                (App Opapp
                  [
                    (Var (Short «odd»));
                    (App (Arith Add IntT) [(Var (Short «k»)); (Lit (IntLit (-1)))])])));
            («odd», «k»,
              (If
                (App (Test Equal IntT) [(Var (Short «k»)); (Lit (IntLit 0))])
                (Con (SOME (Short «False»)) [])
                (App Opapp
                  [
                    (Var (Short «even»));
                    (App (Arith Add IntT) [(Var (Short «k»)); (Lit (IntLit (-1)))])])))])]
      [
        (Dletrec NoLocs
          [(«parity»,«n»,(App Opapp [(Var (Short «even»)); (Var (Short «n»))]))])])
Proof
  EVAL_TAC
QED

(*
  Self recursion does not make the group closed if its base case still needs the
  enclosing parameter.
*)
Theorem test_recursive_self_reference_with_outer_capture[local]:
  comp
    (Dletrec NoLocs
      [
        («run», «n»,
          (Letrec
            [
              («loop», «k»,
                (If
                  (App (Test Equal IntT) [(Var (Short «k»)); (Lit (IntLit 0))])
                  (Var (Short «n»))
                  (App Opapp
                    [
                      (Var (Short «loop»));
                      (App (Arith Add IntT) [(Var (Short «k»)); (Lit (IntLit (-1)))])])))]
            (App Opapp [(Var (Short «loop»)); (Lit (IntLit 3))])))])
  =
    (Dletrec NoLocs
      [
        («run», «n»,
          (Letrec
            [
              («loop», «k»,
                (If
                  (App (Test Equal IntT) [(Var (Short «k»)); (Lit (IntLit 0))])
                  (Var (Short «n»))
                  (App Opapp
                    [
                      (Var (Short «loop»));
                      (App (Arith Add IntT) [(Var (Short «k»)); (Lit (IntLit (-1)))])])))]
            (App Opapp [(Var (Short «loop»)); (Lit (IntLit 3))])))])
Proof
  EVAL_TAC
QED

(*
  After lifting the first h1, a capturing local h1 shadows it. h2 must depend on the
  capturing binding, not the earlier hoisted one.
*)
Theorem test_shadowed_lifted_dependency_is_not_closedish[local]:
  comp
    (Dletrec NoLocs
      [
        («foo», «n»,
          (Letrec
            [(«h1»,«m»,(App (Arith Add IntT) [(Var (Short «m»)); (Lit (IntLit 1))]))]
            (Letrec
              [(«h1»,«m»,(App (Arith Add IntT) [(Var (Short «n»)); (Var (Short «m»))]))]
              (Letrec
                [(«h2»,«k»,(App Opapp [(Var (Short «h1»)); (Var (Short «k»))]))]
                (App Opapp [(Var (Short «h2»)); (Var (Short «n»))])))))])
  =
    (Dlocal
      [
        (Dletrec NoLocs
          [(«h1»,«m»,(App (Arith Add IntT) [(Var (Short «m»)); (Lit (IntLit 1))]))])]
      [
        (Dletrec NoLocs
          [
            («foo», «n»,
              (Letrec
                [
                  («h1», «m»,
                    (App (Arith Add IntT) [(Var (Short «n»)); (Var (Short «m»))]))]
                (Letrec
                  [(«h2»,«k»,(App Opapp [(Var (Short «h1»)); (Var (Short «k»))]))]
                  (App Opapp [(Var (Short «h2»)); (Var (Short «n»))]))))])])
Proof
  EVAL_TAC
QED

(*
  A qualified declaration-level dependency remains available after hoisting a named
  helper through nested local bindings.
*)
Theorem test_closedish_qualified_dependency[local]:
  comp
    (Dletrec NoLocs
      [
        («foo», «n»,
          (Let (SOME «unused») (Lit (IntLit 1))
            (Letrec
              [
                («bar», «m»,
                  (App Opapp
                    [
                      (Var (Long «Library» (Long «Inner» (Short «helper»))));
                      (Var (Short «m»))]))]
              (App Opapp [(Var (Short «bar»)); (Var (Short «n»))]))))])
  =
    (Dlocal
      [
        (Dletrec NoLocs
          [
            («bar», «m»,
              (App Opapp
                [
                  (Var (Long «Library» (Long «Inner» (Short «helper»))));
                  (Var (Short «m»))]))])]
      [
        (Dletrec NoLocs
          [
            («foo», «n»,
              (Let (SOME «unused») (Lit (IntLit 1))
                (App Opapp [(Var (Short «bar»)); (Var (Short «n»))])))])])
Proof
  EVAL_TAC
QED

(*
  All bindings of a nested alias/reference/type pattern remain captures of the local
  closure; only its string can escape.
*)
Theorem test_alias_reference_and_typed_pattern_capture[local]:
  comp
    (Dlet NoLocs (Pvar «match_capture»)
      (Fun «n»
        (Mat (Var (Short «n»))
          [
            (
              (Pas
                (Pcon NONE [(Pvar «x»); (Pref (Ptannot (Pvar «y») (Atvar «a»)))])
                «whole»),
              (Let (SOME «f»)
                (Fun «z»
                  (Con NONE
                    [
                      (Var (Short «x»));
                      (Var (Short «y»));
                      (Var (Short «z»));
                      (Lit (StrLit «inside pattern capture»))]))
                (App Opapp [(Var (Short «f»)); (Var (Short «x»))])))])))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_») (Lit (StrLit «inside pattern capture»)))]
      [
        (Dlet NoLocs (Pvar «match_capture»)
          (Fun «n»
            (Mat (Var (Short «n»))
              [
                (
                  (Pas
                    (Pcon NONE [(Pvar «x»); (Pref (Ptannot (Pvar «y») (Atvar «a»)))])
                    «whole»),
                  (Let (SOME «f»)
                    (Fun «z»
                      (Con NONE
                        [
                          (Var (Short «x»));
                          (Var (Short «y»));
                          (Var (Short «z»));
                          (Var (Short «constant_»))]))
                    (App Opapp [(Var (Short «f»)); (Var (Short «x»))])))])))])
Proof
  EVAL_TAC
QED

(*
  An exception payload is a genuine local capture, while an expensive independent
  handler argument is liftable.
*)
Theorem test_exception_handler_binding_is_a_capture[local]:
  comp
    (Dlet NoLocs (Pvar «catch»)
      (Fun «err»
        (Handle (Raise (Var (Short «err»)))
          [
            ((Pcon (SOME (Short «E»)) [(Pvar «message»)]) ,
              (App Opapp
                [
                  (Fun «x» (Con NONE [(Var (Short «message»)); (Var (Short «x»))]));
                  (Lit (StrLit «handler argument»))]))])))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_») (Lit (StrLit «handler argument»)))]
      [
        (Dlet NoLocs (Pvar «catch»)
          (Fun «err»
            (Handle (Raise (Var (Short «err»)))
              [
                ((Pcon (SOME (Short «E»)) [(Pvar «message»)]) ,
                  (App Opapp
                    [
                      (Fun «x» (Con NONE [(Var (Short «message»)); (Var (Short «x»))]));
                      (Var (Short «constant_»))]))])))])
Proof
  EVAL_TAC
QED

(*
  Keep all construction beneath primitive Equality in place, but resume lifting in
  the following sequence expression.
*)
Theorem test_equality_barrier_is_local_and_transitive[local]:
  comp
    (Dlet NoLocs (Pvar «eq_scope»)
      (Fun «n»
        (Fun «m»
          (Let NONE
            (App Equality
              [
                (Con NONE
                  [
                    (Lit (StrLit «left»));
                    (Con NONE [(Lit (IntLit 1208925819614629174706176))])]);
                (Con NONE
                  [
                    (Lit (StrLit «right»));
                    (Con NONE [(Lit (IntLit 1208925819614629174706176))])])])
            (Lit (StrLit «outside equality»))))))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_») (Lit (StrLit «outside equality»)))]
      [
        (Dlet NoLocs (Pvar «eq_scope»)
          (Fun «n»
            (Fun «m»
              (Let NONE
                (App Equality
                  [
                    (Con NONE
                      [
                        (Lit (StrLit «left»));
                        (Con NONE [(Lit (IntLit 1208925819614629174706176))])]);
                    (Con NONE
                      [
                        (Lit (StrLit «right»));
                        (Con NONE [(Lit (IntLit 1208925819614629174706176))])])])
                (Var (Short «constant_»))))))])
Proof
  EVAL_TAC
QED

(*
  Hoist the immutable payload, never the reference allocation itself or the tuple
  that contains the reference.
*)
Theorem test_reference_allocation_stays_per_call[local]:
  comp
    (Dlet NoLocs (Pvar «allocate»)
      (Fun «n»
        (Let (SOME «r»)
          (App Opref
            [
              (Con NONE
                [
                  (Lit (StrLit «reference payload»));
                  (Lit (IntLit 1208925819614629174706176))])])
          (Con NONE [(Var (Short «r»)); (Var (Short «n»))]))))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_»)
          (Con NONE
            [
              (Lit (StrLit «reference payload»));
              (Lit (IntLit 1208925819614629174706176))]))]
      [
        (Dlet NoLocs (Pvar «allocate»)
          (Fun «n»
            (Let (SOME «r»)
              (App Opref [(Var (Short «constant_»))])
              (Con NONE [(Var (Short «r»)); (Var (Short «n»))]))))])
Proof
  EVAL_TAC
QED

(*
  Hoist two closed anonymous helpers in traversal order while retaining both
  conditional calls.
*)
Theorem test_anonymous_helpers_in_alternative_branches[local]:
  comp
    (Dlet NoLocs (Pvar «branch_helpers»)
      (Fun «flag»
        (If (Var (Short «flag»))
          (App Opapp
            [
              (Fun «x»
                (App (Arith Add IntT) [(Var (Short «x»)); (Lit (IntLit 1))]));
              (Lit (IntLit 10))])
          (App Opapp
            [
              (Fun «y»
                (App (Arith Add IntT) [(Var (Short «y»)); (Lit (IntLit 2))]));
              (Lit (IntLit 20))]))))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_»)
          (Fun «x»
            (App (Arith Add IntT) [(Var (Short «x»)); (Lit (IntLit 1))])));
        (Dlet NoLocs (Pvar «constant__»)
          (Fun «y»
            (App (Arith Add IntT) [(Var (Short «y»)); (Lit (IntLit 2))])))]
      [
        (Dlet NoLocs (Pvar «branch_helpers»)
          (Fun «flag»
            (If (Var (Short «flag»))
              (App Opapp [(Var (Short «constant_»)); (Lit (IntLit 10))])
              (App Opapp [(Var (Short «constant__»)); (Lit (IntLit 20))]))))])
Proof
  EVAL_TAC
QED

(*
  The generated variable must not be captured by an unused parameter named
  constant_. Reserve the binder even without a Var occurrence.
*)
Theorem test_freshness_against_unused_function_parameter[local]:
  comp
    (Dlet NoLocs (Pvar «hygiene»)
      (Fun «constant_»
        (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))])))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant___________»)
          (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))]))]
      [
        (Dlet NoLocs (Pvar «hygiene»)
          (Fun «constant_» (Var (Short «constant___________»))))])
Proof
  EVAL_TAC
QED

(* An unused Let binder can still capture a newly introduced Var two levels below it. *)
Theorem test_freshness_against_unused_nested_let_binder[local]:
  comp
    (Dlet NoLocs (Pvar «hygiene_let»)
      (Fun «n»
        (Let (SOME «constant_») (Lit (IntLit 7))
          (Let (SOME «unused») (Lit (IntLit 9))
            (Con NONE
              [(Var (Short «n»)); (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))])])))))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant___________»)
          (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))]))]
      [
        (Dlet NoLocs (Pvar «hygiene_let»)
          (Fun «n»
            (Let (SOME «constant_») (Lit (IntLit 7))
              (Let (SOME «unused») (Lit (IntLit 9))
                (Con NONE
                  [(Var (Short «n»)); (Var (Short «constant___________»))])))))])
Proof
  EVAL_TAC
QED

(* Pattern aliases reserve their spelling even if their bound value is never read. *)
Theorem test_freshness_against_unused_pattern_alias[local]:
  comp
    (Dlet NoLocs (Pvar «hygiene_match»)
      (Fun «n»
        (Mat (Var (Short «n»))
          [
            (
              (Pas (Pcon NONE [(Pvar «x»); (Pvar «y»)]) «constant_»),
              (Con NONE
                [(Var (Short «x»)); (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))])]))])))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant___________»)
          (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))]))]
      [
        (Dlet NoLocs (Pvar «hygiene_match»)
          (Fun «n»
            (Mat (Var (Short «n»))
              [
                (
                  (Pas (Pcon NONE [(Pvar «x»); (Pvar «y»)]) «constant_»),
                  (Con NONE
                    [(Var (Short «x»)); (Var (Short «constant___________»))]))])))])
Proof
  EVAL_TAC
QED

(*
  Top-level alias names are part of the fresh-name bound, not only the names under
  the alias pattern.
*)
Theorem test_freshness_against_top_level_pattern_alias[local]:
  comp
    (Dlet NoLocs (Pas (Pvar «result») «constant_»)
      (Fun «n» (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))])))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant___________»)
          (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))]))]
      [
        (Dlet NoLocs (Pas (Pvar «result») «constant_»)
          (Fun «n» (Var (Short «constant___________»))))])
Proof
  EVAL_TAC
QED

(*
  An unused exception-handler binding must not capture the hoisted constant at the
  handler result.
*)
Theorem test_freshness_against_unused_exception_payload[local]:
  comp
    (Dlet NoLocs (Pvar «hygiene_handler»)
      (Fun «err»
        (Handle (Raise (Var (Short «err»)))
          [
            (
              (Pcon (SOME (Short «E»)) [(Pvar «constant_»)]),
              (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))]))])))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant___________»)
          (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))]))]
      [
        (Dlet NoLocs (Pvar «hygiene_handler»)
          (Fun «err»
            (Handle (Raise (Var (Short «err»)))
              [
                (
                  (Pcon (SOME (Short «E»)) [(Pvar «constant_»)]),
                  (Var (Short «constant___________»)))])))])
Proof
  EVAL_TAC
QED

(*
  An existing prefixed variable that is used reserves its full spelling; the newly
  introduced name uses the next conservative length bound.
*)
Theorem test_freshness_beyond_existing_prefixed_variable[local]:
  comp
    (Dlet NoLocs (Pvar «reserved»)
      (Fun «n»
        (Let (SOME «constant___») (Var (Short «n»))
          (Con NONE
            [
              (Var (Short «constant___»));
              (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))])]))))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_____________»)
          (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))]))]
      [
        (Dlet NoLocs (Pvar «reserved»)
          (Fun «n»
            (Let (SOME «constant___») (Var (Short «n»))
              (Con NONE
                [(Var (Short «constant___»)); (Var (Short «constant_____________»))]))))])
Proof
  EVAL_TAC
QED

(*
  A qualified constant_ is distinct from a fresh unqualified constant_; retain the
  qualified lookup verbatim.
*)
Theorem test_qualified_name_does_not_capture_generated_short_name[local]:
  comp
    (Dlet NoLocs (Pvar «qualified»)
      (Fun «n»
        (Con NONE
          [
            (Var (Long «M» (Short «constant_»)));
            (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))])])))
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_»)
          (Con NONE [(Lit (IntLit 11)); (Lit (IntLit 12))]))]
      [
        (Dlet NoLocs (Pvar «qualified»)
          (Fun «n»
            (Con NONE
              [(Var (Long «M» (Short «constant_»))); (Var (Short «constant_»))])))])
Proof
  EVAL_TAC
QED

(*
  The bodies of a top-level recursive group share a fresh-name supply and preserve
  their declaration order.
*)
Theorem test_one_fresh_supply_across_declaration_recgroup[local]:
  comp
    (Dletrec NoLocs
      [
        («first»,«x»,(Con NONE [(Var (Short «x»)); (Lit (StrLit «first body»))]));
        («second»,«y»,(Con NONE [(Var (Short «y»)); (Lit (StrLit «second body»))]))])
  =
    (Dlocal
      [
        (Dlet NoLocs (Pvar «constant_») (Lit (StrLit «first body»)));
        (Dlet NoLocs (Pvar «constant__») (Lit (StrLit «second body»)))]
      [
        (Dletrec NoLocs
          [
            («first»,«x»,(Con NONE [(Var (Short «x»)); (Var (Short «constant_»))]));
            («second»,«y»,(Con NONE [(Var (Short «y»)); (Var (Short «constant__»))]))])])
Proof
  EVAL_TAC
QED

(*
  Generated helpers remain inside the declaration they serve; two private Dlocal
  scopes may independently reuse constant_.
*)
Theorem test_module_and_local_declaration_boundaries[local]:
  comp
    (Dmod «M»
      [
        (Dlocal
          [
            (Dlet NoLocs (Pvar «hidden»)
              (Fun «x» (Lit (StrLit «private constant»))))]
          [
            (Dlet NoLocs (Pvar «visible»)
              (Fun «y» (Lit (StrLit «exported constant»))))])])
  =
    (Dmod «M»
      [
        (Dlocal
          [
            (Dlocal
              [
                (Dlet NoLocs (Pvar «constant_») (Lit (StrLit «private constant»)))]
              [
                (Dlet NoLocs (Pvar «hidden»)
                  (Fun «x» (Var (Short «constant_»))))])]
          [
            (Dlocal
              [
                (Dlet NoLocs (Pvar «constant_») (Lit (StrLit «exported constant»)))]
              [
                (Dlet NoLocs (Pvar «visible»)
                  (Fun «y» (Var (Short «constant_»))))])])])
Proof
  EVAL_TAC
QED

Theorem test_named_helper_avoids_enclosing_parameter[local]:
  comp
    (Dletrec NoLocs
      [(«foo»,«x»,
        Let (SOME «x») (Fun «y» (Var (Short «y»))) (Var (Short «x»)))])
  =
    (Dlocal
      [Dlet NoLocs (Pvar «constant_») (Fun «y» (Var (Short «y»)))]
      [Dletrec NoLocs [(«foo»,«x»,Var (Short «constant_»))]])
Proof
  EVAL_TAC
QED

Theorem test_recursive_helper_avoids_enclosing_parameter[local]:
  comp
    (Dletrec NoLocs
      [(«foo»,«x»,
        Letrec [(«x»,«y»,Var (Short «y»))] (Var (Short «x»)))])
  =
    (Dlocal
      [Dletrec NoLocs [(«constant_»,«y»,Var (Short «y»))]]
      [Dletrec NoLocs [(«foo»,«x»,Var (Short «constant_»))]])
Proof
  EVAL_TAC
QED

Theorem test_shadowing_helper_application[local]:
  let prog =
    [Dlocal
      [Dletrec NoLocs
        [(«foo»,«x»,
          Let (SOME «x») (Fun «y» (Var (Short «y»))) (Var (Short «x»)))]]
      [Dlet NoLocs (Pvar «answer»)
        (App Opapp
          [App Opapp [Var (Short «foo»); Lit (IntLit 0)]; Lit (IntLit 9)])]] in
  evaluate_decs (s with clock := 5) <|v := nsEmpty; c := nsEmpty|>
    (source_lift_consts$compile_decs prog) =
    (s with clock := 3,
      Rval <|v := nsBind «answer» (Litv (IntLit 9)) nsEmpty; c := nsEmpty|>) ∧
  evaluate_decs (s with clock := 5) <|v := nsEmpty; c := nsEmpty|> prog =
    (s with clock := 3,
      Rval <|v := nsBind «answer» (Litv (IntLit 9)) nsEmpty; c := nsEmpty|>)
Proof
  EVAL_TAC
QED

Theorem test_repeated_shadowing_reserves_original_name[local]:
  comp
    (Dlet NoLocs (Pvar «test»)
      (Fun «z»
        (Let (SOME «foo») (Lit (IntLit 0))
          (Let (SOME «foo») (Fun «y» (Var (Short «y»)))
            (Let (SOME «foo») (Fun «y» (Lit (IntLit 1)))
              (Var (Short «foo»)))))))
  =
    (Dlocal
      [Dlet NoLocs (Pvar «constant_») (Fun «y» (Var (Short «y»)));
       Dlet NoLocs (Pvar «constant__») (Fun «y» (Lit (IntLit 1)))]
      [Dlet NoLocs (Pvar «test»)
        (Fun «z»
          (Let (SOME «foo») (Lit (IntLit 0)) (Var (Short «constant__»))))])
Proof
  EVAL_TAC
QED

Theorem test_repeated_shadowing_helper_application[local]:
  let prog =
    [Dlocal
      [Dlet NoLocs (Pvar «test»)
        (Fun «z»
          (Let (SOME «foo») (Lit (IntLit 0))
            (Let (SOME «foo») (Fun «y» (Var (Short «y»)))
              (Let (SOME «foo») (Fun «y» (Lit (IntLit 1)))
                (Var (Short «foo»))))))]
      [Dlet NoLocs (Pvar «answer»)
        (App Opapp
          [App Opapp [Var (Short «test»); Lit (IntLit 0)]; Lit (IntLit 9)])]] in
  evaluate_decs (s with clock := 5) <|v := nsEmpty; c := nsEmpty|>
    (source_lift_consts$compile_decs prog) =
    (s with clock := 3,
      Rval <|v := nsBind «answer» (Litv (IntLit 1)) nsEmpty; c := nsEmpty|>) ∧
  evaluate_decs (s with clock := 5) <|v := nsEmpty; c := nsEmpty|> prog =
    (s with clock := 3,
      Rval <|v := nsBind «answer» (Litv (IntLit 1)) nsEmpty; c := nsEmpty|>)
Proof
  EVAL_TAC
QED

(* --------------------------------------------------------- *
    Some simple sanity tests
 * --------------------------------------------------------- *)

Theorem test1[local]: (* no lift outside of closures *)
  compile_dec (Dlet NoLocs (Pvar «a») (Con NONE [Lit (IntLit 1); Lit (IntLit 2)]))
  =
  Dlet NoLocs (Pvar «a») (Con NONE [Lit (IntLit 1); Lit (IntLit 2)])
Proof
  EVAL_TAC
QED

Theorem test2[local]: (* constants lifted from within closures *)
  compile_dec (Dlet NoLocs (Pvar «a»)
    (Fun «a» (Con NONE [Lit (IntLit 1); Lit (IntLit 2)])))
  =
  Dlocal
     [Dlet NoLocs (Pvar «constant_») (Con NONE [Lit (IntLit 1); Lit (IntLit 2)])]
     [Dlet NoLocs (Pvar «a») (Fun «a» (Var (Short «constant_»)))]
Proof
  EVAL_TAC
QED

Theorem test3[local]: (* constants are *not* lifted under Equality *)
  compile_dec
    (Dlet NoLocs (Pvar «a»)
      (Fun «a» (App Equality [Var (Short «a»);
                              Con NONE [Lit (IntLit 1); Lit (IntLit 2)]])))
  =
    (Dlet NoLocs (Pvar «a»)
      (Fun «a» (App Equality [Var (Short «a»);
                              Con NONE [Lit (IntLit 1); Lit (IntLit 2)]])))
Proof
  EVAL_TAC
QED

Theorem test4[local]: (* constants are lifted under App *)
  compile_dec
    (Dlet NoLocs (Pvar «a»)
      (Fun «a» (App ListAppend [Var (Short «a»);
                                Con NONE [Lit (IntLit 1); Lit (IntLit 2)]])))
  =
  Dlocal
     [Dlet NoLocs (Pvar «constant_»)
        (Con NONE [Lit (IntLit 1); Lit (IntLit 2)])]
     [Dlet NoLocs (Pvar «a»)
        (Fun «a» (App ListAppend [Var (Short «a»); Var (Short «constant_»)]))]
Proof
  EVAL_TAC
QED

Theorem test5[local]: (* curried functions are not taken apart *)
  compile_dec
    (Dlet NoLocs (Pvar «a») (Fun «a» (Fun «b» (Lit (IntLit 5)))))
  =
  Dlet NoLocs (Pvar «a») (Fun «a» (Fun «b» (Lit (IntLit 5))))
Proof
  EVAL_TAC
QED

Theorem test6[local]: (* functions inside constant data are lifted separately *)
  compile_dec
    (Dlet NoLocs (Pvar «a») (Fun «a» (Con NONE [Fun «b» (Lit (IntLit 5))])))
  =
  Dlocal
     [Dlet NoLocs (Pvar «constant_») (Fun «b» (Lit (IntLit 5)));
      Dlet NoLocs (Pvar «constant__») (Con NONE [Var (Short «constant_»)])]
     [Dlet NoLocs (Pvar «a») (Fun «a» (Var (Short «constant__»)))]
Proof
  EVAL_TAC
QED
