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
    in String.fields f arrayString end`

val st = ml_progLib.add_prog w8arrayToStrings pick_name (get_ml_prog_state())

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


val commandLine_fun_def = Define `
  commandLine_fun = (\i bytes s. case (bytes,s) of
      | (b, Str commandLine) =>
        if i = "getArgs" then
          if (LENGTH b = 256) then
            if (LENGTH commandLine < 257) then 
              SOME (((MAP (n2w o ORD) commandLine) ++ DROP (LENGTH commandLine) b), Str commandLine)
            else
              SOME ((MAP (n2w o ORD) (TAKE 256 commandLine)), Str commandLine)
          else NONE
        else NONE 
      | _ => NONE)`

val COMMANDLINE_def = Define `
  COMMANDLINE (cl:string) =
    IO (Str cl) commandLine_fun ["getArgs"] *
    SEP_EXISTS w. W8ARRAY commandLine_state [w]` 

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
        app (p:'ffi ffi_proj) ^(fetch_v "w8arrayToStrings" st) [av]
        (W8ARRAY av a)
        (POSTv strlv. &LIST_TYPE STRING_TYPE (fields (\x. x = (CHR 0)) (implode (MAP (CHR o w2n) a))) strlv)`
    xcf "w8arrayToStrings" st
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
      >- ( 
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
       `!c cv.
       CHAR c cv ==>
       app p g [cv] 
       (W8ARRAY av a)
       (POSTv bool. &BOOL (ORD c = 0) boolv * W8ARRAY av a)`
        >-(rpt strip_tac \\ first_x_assum match_mp_tac 
          \\ xlet `POSTv cordv. &NUM (ORD c) cordv * W8ARRAY av a`
            >-(xapp \\ xsimpl \\ instantiate)
          \\ xapp \\ xsimpl \\ qexists_tac `0` \\ qexists_tac `ORD c` \\ qexists_tac `NUM`
           
            INT_def
           NUM
           Arrow_eq_app_basic
      app_to_Arrow_rule

      DB.find""
      app_def
      app_basic_def
      app_of_Arrow_rule

fetch_v "Word8Array.sub" st

CONV_TAC(STRIP_QUANT_CONV(LAND_CONV(reduce_conv)))
fetch_v "Array.length" st

DB.find "PAIR_TYPE"

DB.find "equalityType_NUM_BOOL"
DB.find "explode_11"
DB.find "mlstring"
(*AIM: to be able to define echo using the arguments function so that
  `!cl. (*some specification about length of cl being less than 256*) ==>
  app (p:'ffi ffi_proj) echo_v [uv] (COMMANDLINE cl * STDOUT out)
  (POSTv u. COMMANDLINE cl * STDOUT (out ++ (CONCAT (MAP implode (arguments cl)))))`

  is true *)
*)
val _ = export_theory()

