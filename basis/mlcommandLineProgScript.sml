open preamble
     ml_translatorLib ml_progLib
     cfTheory cfHeapsTheory cfTacticsLib cfTacticsBaseLib basisFunctionsLib
     mlcharioProgTheory ml_progLib ml_translatorTheory

val _ = new_theory "mlcommandLineProg";

val _ = translation_extends "mlcharioProg";

val _ = ml_prog_update (open_module "commandLine")
val e = ``(App Aw8alloc [Lit (IntLit 256); Lit (Word8 0w)])``

val _ = ml_prog_update (add_Dlet (derive_eval_thm "commandLine_state" e) "commandLine_state" [])

val w8arrayToStrings = process_topdecs
  `fun w8arrayToStrings arr =
    let
      val arrayList = List.tabulate (Word8Array.length arr) (fn x => Char.chr (Word8.toInt (Word8Array.sub arr x)))
      val arrayString = String.implode arrayList
      fun f x = (Char.ord x = 0)
    in String.tokens f arrayString end`

val res = ml_prog_update (ml_progLib.add_prog w8arrayToStrings pick_name)

val e =
  ``Let NONE (App (FFI "getArgs") [Var (Short "commandLine_state")])
      (LetApps "ss" (Short "w8arrayToStrings") [Var (Short "commandLine_state")]
        (Apps [Var (Long "List" "hd"); Var (Short "ss")]))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update(add_Dlet_Fun ``"name"`` ``"u"`` e "name_v")

val e =
  ``Let NONE (App (FFI "getArgs") [Var (Short "commandLine_state")])
      (LetApps "ss" (Short "w8arrayToStrings") [Var (Short "commandLine_state")]
        (Apps [Var (Long "List" "tl"); Var (Short "ss")]))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update(add_Dlet_Fun ``"arguments"`` ``"u"`` e "arguments_v")

val _ = ml_prog_update (close_module NONE);


(* TODO: define more generally (it's used in cat example too I think) *)
val destStr_def = Define`destStr (Str s) = s`;
val isStr_def = Define`(isStr (Str _) = T) ∧ (isStr _ = F)`;
 val _ = export_rewrites["isStr_def","destStr_def"];

val commandLine_fun_def = Define `
  commandLine_fun = (\i bytes s. case (bytes,s) of
      | (b, List commandLineStrings) =>
        if i = "getArgs" ∧ LENGTH b = 256 ∧ EVERY isStr commandLineStrings then
            let commandLine = FLAT (MAP (\s. destStr s ++ [CHR 0]) commandLineStrings) in
            if (LENGTH commandLine < 257) then 
              SOME (((MAP (n2w o ORD) commandLine) ++ DROP (LENGTH commandLine) b), List commandLineStrings)
            else
              SOME ((MAP (n2w o ORD) (TAKE 256 commandLine)), List commandLineStrings)
        else NONE 
      | _ => NONE)`

val COMMANDLINE_def = Define `
  COMMANDLINE (cl:string list) =
    IO (List (MAP Str cl)) commandLine_fun ["getArgs"] *
    SEP_EXISTS w. W8ARRAY commandLine_state w * &(LENGTH w = 256)` 

val st = get_ml_prog_state()
(*
options:
  - ask Magnus + Armael how to prove the spec below
  - write/use a custom (non higher-order) version of tabulate for this module instead
*)

val tabulate_spec = Q.store_thm("tabulate_spec",
  `!f fv A heap_inv n nv.
    NUM n nv /\ ls = GENLIST f n /\
    (!i iv. NUM i iv /\ i < n ==> app p fv [iv] heap_inv (POSTv v. &(A (f i) v) * heap_inv))
    ==>
    app p ^(fetch_v "List.tabulate" st) [nv; fv] heap_inv (POSTv lv. &LIST_TYPE A ls lv * heap_inv)`,
    cheat);

(*
  can't prove this with xcf because tabulate comes from the translator so is
  not in A normal form, but CF tactics require code in A normal form

  ntac 4 gen_tac
  \\ Induct
  >- (
    rw[]
    \\ xcf "List.tabulate" st
    \\ xpull_check_not_needed
    \\ head_unfold cf_if_def
    \\ irule local_elim
    \\ hnf
    \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV(reduce_conv)))

    \\ app_
    val (asl,w) = top_goal()
    spec_kind_for (#2 (goal_app_infos w))
    xapp_spec
    rw[app_def]
    DB.find"exp2v_def"
    app_basic_def
    hide_environments false
*)

val eq_v_thm = fetch "mlbasicsProg" "eq_v_thm"
val eq_num_v_thm = save_thm("eq_num_v_thm",
        MATCH_MP (DISCH_ALL eq_v_thm) (EqualityType_NUM_BOOL |> CONJUNCT1))

val w8arrayToStrings_spec = Q.store_thm ("w8arrayToStrings_spec",
    `!av a.
        app (p:'ffi ffi_proj) ^(fetch_v "commandLine.w8arrayToStrings" st) [av]
        (W8ARRAY av a)
        (POSTv strlv. &LIST_TYPE STRING_TYPE (tokens (\x. x = (CHR 0)) (implode (MAP (CHR o w2n) a))) strlv * W8ARRAY av a)`,
    xcf "commandLine.w8arrayToStrings" st
    \\ xfun_spec `e`
      `!x xv.
        NUM x xv /\ x < LENGTH a ==>
        app p e [xv] 
        (W8ARRAY av a)
        (POSTv wordv. &CHAR (CHR (w2n (EL x a))) wordv * W8ARRAY av a)`
      >-(rpt strip_tac \\ first_x_assum match_mp_tac
        \\ xlet `POSTv subv. & WORD (EL x a) subv * W8ARRAY av a`
          >-(xapp \\ fs[])
        \\ xlet `POSTv intv. & NUM (w2n (EL x a)) intv * W8ARRAY av a`
          >-(xapp \\ xsimpl \\ instantiate)
        \\ xapp \\ xsimpl \\ instantiate \\ rw[w2n_lt_256])
      \\ xlet `POSTv lenv. & NUM (LENGTH a) lenv * W8ARRAY av a`
        >-(xapp)
      \\ xlet `POSTv lv. &LIST_TYPE CHAR (MAP (CHR o w2n) a) lv * W8ARRAY av a`
      >-( 
           (*
           `MAP (CHR o w2n) a = GENLIST (\x. CHR(w2n(EL x a))) (LENGTH a)` by simp[LIST_EQ_REWRITE,EL_MAP]
           \\ pop_assum SUBST1_TAC
           *)
           xapp
        \\ simp[LIST_EQ_REWRITE,EL_MAP]
        \\ qexists_tac`\x. CHR(w2n(EL x a))`
        \\ simp[]
      )
      \\ xlet `POSTv strv. &STRING_TYPE (implode (MAP (CHR o w2n) a)) strv * W8ARRAY av a`
        >-(xapp \\ xsimpl \\ instantiate)
      \\ xfun_spec `g`
          `(CHAR --> BOOL) (\x. x = (CHR 0)) g`
          >- (
            Q.ISPEC_THEN`p`(fn th => CONV_TAC(REWR_CONV th)) (Q.GEN`p`cfAppTheory.Arrow_eq_app_basic)
            \\ fs[cfAppTheory.app_def] \\ rw[]
            \\ first_x_assum match_mp_tac
            \\ xlet `POSTv cordv. &NUM (ORD x) cordv`
            >- ( xapp \\ fs[] )
            \\ xapp_spec eq_num_v_thm \\ xsimpl \\ instantiate
            \\ fs[BOOL_def]
            \\ Cases_on`x` \\ fs[] )
      \\ xapp \\ xsimpl \\ instantiate);


val map_app_last_thm = Q.prove(
  `!ls a. ls <> [] ==> ?l. FLAT(MAP (\x. x ++ [a]) ls) = l ++ [a]`,
  Induct \\ rw[] \\ first_x_assum(qspecl_then [`a`] mp_tac) \\ Cases_on `ls`
  \\ rw[] \\ qexists_tac `h++[a]++l` \\ rw[] 
);

val map_app_last_Str = Q.prove(
  `!ls. ls <> [] ==> ?l.
      CONCAT(MAP(\s. STRCAT (destStr s) "\^@") (MAP Str ls)) =  l ++ [CHR 0]`,
  Induct \\ rw[] \\ Cases_on `ls` \\ rw[] \\ qexists_tac `h++[CHR 0]++l` \\ rw[]
);

val map_app_count_thm = Q.prove(
  `!ls a. ~(EXISTS (\x. x = a) (FLAT ls)) ==> 
    LIST_ELEM_COUNT a (FLAT(MAP (\y. y ++ [a]) ls)) = LENGTH ls`,
    Induct \\ rw[LIST_ELEM_COUNT_DEF, FILTER_APPEND_DISTRIB]
    \\ fs[o_DEF, GSYM FILTER_EQ_NIL, LIST_ELEM_COUNT_DEF] 
);

val map_app_count_Str = Q.prove(
  `!ls. ~(EXISTS (\x. x = #"\^@") (FLAT ls)) ==> 
    LIST_ELEM_COUNT #"\^@" (CONCAT(MAP (\s. STRCAT (destStr s) "\^@") (MAP Str ls) )) = LENGTH ls`,
    Induct \\ rw[LIST_ELEM_COUNT_DEF, FILTER_APPEND_DISTRIB]
    \\ fs[o_DEF, GSYM FILTER_EQ_NIL, LIST_ELEM_COUNT_DEF] 
);


(* Need to include that cl has no null characters 
val commandLine_name_spec = Q.store_thm("commandLine_name_spec",
  `UNIT_TYPE u uv /\ (cl <> []) ==>
    app (p:'ffi ffi_proj) ^(fetch_v "commandLine.name" st) [uv]
    (COMMANDLINE cl)
    (POSTv namev. & STRING_TYPE (implode (HD cl)) namev * COMMANDLINE cl)`,
    xcf "commandLine.name" st
    \\ fs [COMMANDLINE_def] \\ xpull
    \\ Cases_on `LENGTH (MAP ((n2w:num -> word8) o ORD) (FLAT (MAP (\s. (destStr s) ++ [CHR 0]) (MAP Str cl)))) < 257` 
      >-(
        qmatch_assum_abbrev_tac `LENGTH args < 257` 
        \\ xlet `POSTv zv. IO (List (MAP Str cl)) commandLine_fun ["getArgs"] * 
        W8ARRAY commandLine_state (args ++ DROP (LENGTH args) w) * & (UNIT_TYPE () zv)`
        >-(xffi \\ fs [EVAL ``commandLine_state``, COMMANDLINE_def]
          \\ map_every qexists_tac [`w`,  `emp`, `args ++ DROP (LENGTH args) w`, `List (MAP Str cl)`, `List (MAP Str cl)`, `commandLine_fun`, `["getArgs"]`]
          \\ xsimpl \\ fs[commandLine_fun_def, Abbr `args`] \\ simp[EVERY_MAP])

        (* \\ xlet `POSTv strlv. &LIST_TYPE STRING_TYPE (MAP implode cl ++ [implode (MAP (CHR o w2n) (DROP (LENGTH args) w))]) strlv` *) 
        \\ xlet `POSTv strlv. SEP_EXISTS ss. &LIST_TYPE STRING_TYPE ss strlv * & (TAKE (LENGTH cl) ss = MAP implode cl)`  
        >-(
          xapp \\ xsimpl 
          \\ qexists_tac `IO (List (MAP Str cl)) commandLine_fun ["getArgs"]` 
          \\ qexists_tac `args ++ DROP (LENGTH args) w`
          \\ fs[EVAL ``commandLine_state``] \\ xsimpl
          \\ rpt strip_tac \\ instantiate 
          \\ fs[Abbr `args`]
          \\ rw[map_app_last_Str]
          \\ rfs[mlstringTheory.tokens_def, mlstringTheory.tokens_aux_def]
          \\ cheat
          )
        \\ xapp \\ xsimpl \\ qexists_tac `ss`
          


          \\ qexists_tac `IO (Str cl) commandLine_fun ["getArgs"]` \\ qexists_tac `MAP (n2w o ORD) cl ++ DROP (LENGTH cl) w` 
          \\ rw [EVAL ``commandLine_state``] \\ xsimpl)
        \\ instantiate

mlstringTheory.tokens_filter


DB.match[]`` ``
DB.match[]``MAP (MAP _) _`` 
DB.match[]``MAP _ (FLAT _) = FLAT (MAP _ _)``
  \\ xapp_prepare_goal
        val (asl, w) = top_goal()
        val (ffi_ty, f) = goal_app_infos w
        xspec ffi_ty f xapp_xapply_no_simpl
        xspec_in_db f

        is_arrow_spec_for f (concl mllistProgTheory.hd_v_thm)
        val tm = ()

DB.find"n2w"

val hd1_v_thm = save_thm("hd1_v_thm",
  mllistProgTheory.hd_v_thm |> |> UNDISCH_ALL)


        goal_app_infos 


        xapp_xapply_no_simpl
        xspec ffi_ty f 
        \\ xapp_prepare_goal
        val (asl,w) = top_goal()
    spec_kind_for (#2 (goal_app_infos w))
    xapp_spec
        goal_app_infos
        \\ tmtac
       
fetch_v "List.hd" st


        \\ xsimpl
        \\ `MEM "getArgs" ["getArgs"]` by EVAL_TAC \\ fs[commandLine_fun_def] \\ instantiate
      )
    \\ IO (Str cl) commandLine_fun ["getArgs"] * W8ARRAY commandLine_state [w]`
    \\ xlet `POSTv zv. W8ARRAY 
DB.find "REPLICATE"
val commandLine_arguments_spec = Q.store_thm("commandLine_arguments_spec",
    `UNIT_TYPE u uv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "commandLine.name" (hi())) [uv]
    (COMMANDLINE cl)
    (POSTv namev. & STRING_TYPE (tl (tokens (\x. x = (CHR 0)) cl)) namev * COMMANDLINE cl)`
    
*)
(*AIM: to be able to define echo using the arguments function so that
  `!cl. (*some specification about length of cl being less than 256*) ==>
  app (p:'ffi ffi_proj) echo_v [uv] (COMMANDLINE cl * STDOUT out)
  (POSTv u. COMMANDLINE cl * STDOUT (out ++ (CONCAT (MAP implode (arguments cl)))))`

  is true *)
*)
val _ = export_theory()

