open preamble
open ml_translatorTheory ml_translatorLib semanticPrimitivesTheory evaluatePropsTheory
open cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib ml_progLib
local open std_preludeTheory in end

val _ = new_theory "ioProg"

val _ = translation_extends "std_prelude";


(* setup *)

fun get_module_prefix () = let
  val mod_tm = ml_progLib.get_thm (get_ml_prog_state ())
               |> concl |> rator |> rator |> rand
  in if optionSyntax.is_none mod_tm then "" else
       stringSyntax.fromHOLstring (mod_tm |> rand |> rator |> rand) ^ "_"
  end

fun trans ml_name q = let
  val rhs = Term q
  val prefix = get_module_prefix ()
  val tm = mk_eq(mk_var(prefix ^ pick_name ml_name,type_of rhs),rhs)
  val def = Define `^tm`
  val _ = (next_ml_names := [ml_name])
  val v_thm = translate (def |> SIMP_RULE std_ss [FUN_EQ_THM])
  val v_thm = v_thm |> REWRITE_RULE [def]
                    |> CONV_RULE (DEPTH_CONV ETA_CONV)
  val v_name = v_thm |> concl |> rand |> dest_const |> fst
  (* evaluate precondition *)
  val pat = PRECONDITION_def |> SPEC_ALL |> GSYM |> concl |> rand
  fun PRECOND_CONV c tm =
    if can (match_term pat) tm then RAND_CONV c tm else NO_CONV tm
  val v_thm = v_thm |> DISCH_ALL
                    |> CONV_RULE (ONCE_DEPTH_CONV (PRECOND_CONV EVAL))
                    |> UNDISCH_ALL
  val _ = save_thm(v_name ^ "_thm",v_thm)
  in v_thm end

fun append_prog tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  in ml_prog_update (ml_progLib.add_prog tm pick_name) end

fun append_dec tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  in ml_prog_update (ml_progLib.add_dec tm pick_name) end

fun append_decs tm = let
  val tm = QCONV EVAL tm |> concl |> rand
  val tms = fst (listSyntax.dest_list tm)
  in (map append_dec tms; ()) end

fun basis_st () = get_ml_prog_state ()

val _ = Define `
  mk_binop name prim = Dlet (Pvar name)
    (Fun "x" (Fun "y" (App prim [Var (Short "x"); Var (Short "y")])))`;

val _ = Define `
  mk_unop name prim = Dlet (Pvar name)
    (Fun "x" (App prim [Var (Short "x")]))`;


(* Word8 module -- translated *)

val _ = ml_prog_update (open_module "Word8");

val _ = append_dec ``Dtabbrev [] "word" (Tapp [] TC_word8)``;
val _ = trans "fromInt" `n2w:num->word8`
val _ = trans "toInt" `w2n:word8->num`

val _ = ml_prog_update (close_module NONE);


(* Word8Array module -- CF verified *)

val _ = ml_prog_update (open_module "Word8Array");

val _ = append_decs
   ``[mk_binop "array" Aw8alloc;
      mk_binop "sub" Aw8sub;
      mk_unop "length" Aw8length;
      Dlet (Pvar "update") (Fun "x" (Fun "y" (Fun "z"
        (App Aw8update [Var (Short "x"); Var (Short "y"); Var (Short "z")])))) ]``

val _ = ml_prog_update (close_module NONE);

fun prove_array_spec op_name =
  xcf op_name (basis_st()) \\ TRY xpull \\
  fs [cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def, cf_aw8update_def,
      cf_aalloc_def, cf_asub_def, cf_alength_def, cf_aupdate_def] \\
  irule local_elim \\ reduce_tac \\
  fs [app_aw8alloc_def, app_aw8sub_def, app_aw8length_def, app_aw8update_def,
      app_aalloc_def, app_asub_def, app_alength_def, app_aupdate_def] \\
  xsimpl \\ fs [INT_def, NUM_def, WORD_def, w2w_def, UNIT_TYPE_def] \\
  TRY (simp_tac (arith_ss ++ intSimps.INT_ARITH_ss) [])

val w8array_alloc_spec = Q.store_thm ("w8array_alloc_spec",
  `!n nv w wv.
     NUM n nv /\ WORD w wv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.array" (basis_st())) [nv; wv]
       emp (POSTv v. W8ARRAY v (REPLICATE n w))`,
  prove_array_spec "Word8Array.array");

val w8array_sub_spec = Q.store_thm ("w8array_sub_spec",
  `!a av n nv.
     NUM n nv /\ n < LENGTH a ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.sub" (basis_st())) [av; nv]
       (W8ARRAY av a) (POSTv v. cond (WORD (EL n a) v) * W8ARRAY av a)`,
  prove_array_spec "Word8Array.sub");

val w8array_length_spec = Q.store_thm ("w8array_length_spec",
  `!a av.
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.length" (basis_st())) [av]
       (W8ARRAY av a) (POSTv v. cond (NUM (LENGTH a) v) * W8ARRAY av a)`,
  prove_array_spec "Word8Array.length");

val w8array_update_spec = Q.store_thm ("w8array_update_spec",
  `!a av n nv w wv.
     NUM n nv /\ n < LENGTH a /\ WORD w wv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "Word8Array.update" (basis_st()))
       [av; nv; wv]
       (W8ARRAY av a)
       (POSTv v. cond (UNIT_TYPE () v) * W8ARRAY av (LUPDATE w n a))`,
  prove_array_spec "Word8Array.update");


(* Char module -- translated *)

val _ = ml_prog_update (open_module "Char");

val _ = append_dec ``Dtabbrev [] "char" (Tapp [] TC_char)``;
val _ = trans "ord" `ORD`
val _ = trans "chr" `CHR`

val _ = ml_prog_update (close_module NONE);

val _ = trans "bool_of_byte" `\(w:word8). w <> 0w`
val _ = trans "char_of_byte" `\(w:word8). CHR (w2n w)`

val char_of_byte_side = Q.store_thm("char_of_byte_side",
  `char_of_byte_side w`,
  metis_tac [fetch"-" "char_of_byte_side_def",w2n_lt,EVAL ``dimword(:8)``]);

(* CharIO -- CF verified *)

(*

  val write = bytarray [0w];
  val write = fn c =>
    val _ = (write[0] := c)
    in FFI "putChar" write end

*)

val _ = ml_prog_update (open_module "CharIO");

fun derive_eval_thm v_name e = let
  val th = get_ml_prog_state () |> get_thm
  val th = MATCH_MP ml_progTheory.ML_code_NONE_Dlet_var th
           handle HOL_ERR _ =>
           MATCH_MP ml_progTheory.ML_code_SOME_Dlet_var th
  val goal = th |> SPEC e |> SPEC_ALL |> concl |> dest_imp |> fst
  val lemma = goal
    |> (NCONV 50 (SIMP_CONV (srw_ss()) [Once bigStepTheory.evaluate_cases,
            PULL_EXISTS,do_app_def,store_alloc_def,LET_THM]) THENC EVAL)
  val v_thm = prove(mk_imp(lemma |> concl |> rand,goal),fs [lemma])
                 |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL
  val v_tm = v_thm |> concl |> rand |> rand |> rand
  val v_def = define_abbrev true v_name v_tm
  in v_thm |> REWRITE_RULE [GSYM v_def] end

val e = ``(App Aw8alloc [Lit (IntLit 2); Lit (Word8 0w)])``

val _ = ml_prog_update (add_Dlet (derive_eval_thm "read_state_loc" e) "read_state" [])

val e = ``(App Aw8alloc [Lit (IntLit 1); Lit (Word8 0w)])``

val _ = ml_prog_update (add_Dlet (derive_eval_thm "write_state_loc" e) "write_state" [])

val Apps_def = tDefine "Apps" `
  (Apps [x;y] = App Opapp [x;y]) /\
  (Apps [] = ARB) /\
  (Apps xs = App Opapp [Apps (FRONT xs); LAST xs])`
  (WF_REL_TAC `measure LENGTH` \\ fs [LENGTH_FRONT]);

val LetApps_def = Define `
  LetApps n f args = Let (SOME n) (Apps (Var f::args))`;

val e =
  ``Let NONE (App (FFI "getChar") [Var (Short "read_state")])
     (LetApps "c" (Long "Word8Array" "sub") [Var (Short "read_state");  Lit (IntLit 0)]
       (Apps [Var (Short "char_of_byte"); Var (Short "c")]))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update (add_Dlet_Fun ``"read"`` ``"u"`` e "read_v")

val e =
  ``LetApps "f" (Long "Word8Array" "sub") [Var (Short "read_state"); Lit (IntLit 1)]
      (Apps [Var (Short "bool_of_byte"); Var (Short "f")])``
  |> EVAL |> concl |> rand

val _ = ml_prog_update (add_Dlet_Fun ``"read_failed"`` ``"u"`` e "read_failed_v")

val e =
  ``Let (SOME "c") (Apps [Var (Long "Word8Array" "update");
                          Var (Short "write_state");
                          Lit (IntLit 0); Var (Short "c")])
      (Let NONE (App (FFI "putChar") [Var (Short "write_state")]) (Var (Short "c")))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update (add_Dlet_Fun ``"write"`` ``"c"`` e "write_v")

val _ = ml_prog_update (close_module NONE);

val stdin_fun_def = Define `
  stdin_fun = (\i bytes s. case (bytes,s) of
                    | ([b;f],Str input) =>
                         if i = "getChar" then (* read *)
                           if input = "" then
                             SOME ([b;1w],Str input)
                           else (* i = "putChar" *)
                             SOME ([n2w (ORD (HD input)); 0w],Str (TL input))
                         else NONE
                    | _ => NONE)`

val stdout_fun_def = Define `
  stdout_fun = (\_ bytes s. case (bytes,s) of (* write *)
                    | ([w],Str output) => SOME ([w],Str (output ++ [CHR (w2n w)]))
                    | _ => NONE)`

val STDIN_def = Define `
  STDIN input read_failed =
    IO (Str input) stdin_fun ["getChar"] *
    SEP_EXISTS w. W8ARRAY read_state_loc [w;if read_failed then 1w else 0w]`;

val STDOUT_def = Define `
  STDOUT (output:word8 list) =
    IO (Str (MAP (CHR o w2n) output)) stdout_fun ["putChar"] *
    SEP_EXISTS w. W8ARRAY write_state_loc [w]`;

val w2n_lt_256 =
  w2n_lt |> INST_TYPE [``:'a``|->``:8``]
         |> SIMP_RULE std_ss [EVAL ``dimword (:8)``]

val read_spec = Q.store_thm ("read_spec",
  `UNIT_TYPE u uv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "CharIO.read" (basis_st()))
       [uv]
       (STDIN input read_failed)
       (POSTv cv. if input = "" then STDIN input T else
                  cond (CHAR (HD input) cv) * STDIN (TL input) F)`,
  xcf "CharIO.read" (basis_st())
  \\ Cases_on`input = ""` \\ fs[]
  >- (
    fs[STDIN_def] \\ xpull
    \\ xlet `POSTv x. STDIN "" T * cond (UNIT_TYPE () x)`
    >- (
      xffi
      \\ fs[STDIN_def, EVAL ``read_state_loc``]
      \\ `MEM "getChar" ["getChar"]` by simp[] \\ instantiate \\ xsimpl
      \\ fs[stdin_fun_def] )
    \\ fs[STDIN_def] \\ xpull
    \\ xlet `POSTv x. STDIN "" T * cond (WORD (w:word8) x)`
    >- (
      xapp \\ xsimpl \\ fs[STDIN_def]
      \\ fs[EVAL``read_state_loc``] \\ xsimpl)
    \\ rw[STDIN_def] \\ xpull
    \\ xapp \\ xsimpl \\ instantiate
    \\ simp[w2n_lt_256] )
  \\ fs[STDIN_def] \\ xpull
  \\ xlet `POSTv x. IO (Str (TL input)) stdin_fun [1] *
                    W8ARRAY read_state_loc [n2w (ORD (HD input)); 0w]`
  >- (
    xffi
    \\ fs[STDIN_def, EVAL ``read_state_loc``]
    \\ `MEM "getChar" ["getChar"]` by simp[] \\ instantiate \\ xsimpl
    \\ fs[stdin_fun_def] )
  \\ xlet `POSTv x. STDIN (TL input) F * cond (WORD ((n2w(ORD(HD input))):word8) x)`
  >- (
    xapp \\ xsimpl \\ fs[STDIN_def]
    \\ fs[EVAL``read_state_loc``] \\ xsimpl)
  \\ rw[STDIN_def] \\ xpull
  \\ xapp \\ xsimpl \\ instantiate
  \\ simp[CHR_ORD,ORD_BOUND])

val read_failed_spec = Q.store_thm("read_failed_spec",
  `UNIT_TYPE u uv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "CharIO.read_failed" (basis_st()))
      [uv]
      (STDIN input read_failed)
      (POSTv bv. STDIN input read_failed * cond (BOOL read_failed bv))`,
  xcf "CharIO.read_failed" (basis_st())
  \\ fs[STDIN_def] \\ xpull
  \\ xlet `POSTv x. STDIN input read_failed * cond (WORD (if read_failed then 1w else (0w:word8)) x)`
  >- (
    xapp
    \\ fs[STDIN_def]
    \\ fs[EVAL``read_state_loc``]
    \\ xsimpl)
  \\ fs[STDIN_def] \\ xpull
  \\ xapp
  \\ instantiate
  \\ xsimpl
  \\ rw[]);

val write_spec = Q.store_thm ("write_spec",
  `WORD c cv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "CharIO.write" (basis_st()))
       [cv]
       (STDOUT output)
       (POSTv uv. cond (UNIT_TYPE () uv) * STDOUT (output ++ [c]))`,
  xcf "CharIO.write" (basis_st())
  \\ fs [STDOUT_def] \\ xpull
  \\ xlet `POSTv zv. IO (Str (MAP (CHR o w2n) output)) stdout_fun [0] * W8ARRAY write_state_loc [c] *
                     & (UNIT_TYPE () zv)`
  THEN1
   (xapp \\ xsimpl \\ fs [EVAL ``write_state_loc``]
    \\ instantiate \\ xsimpl \\ EVAL_TAC \\ fs [])
  \\ xlet `POSTv _. IO (Str (MAP (CHR o w2n) (output ++ [c]))) stdout_fun [0] * W8ARRAY write_state_loc [c]`
  THEN1
   (xffi
    \\ fs [EVAL ``write_state_loc``, STDOUT_def]
    \\ `MEM "putChar" ["putChar"]` by EVAL_TAC \\ instantiate \\ xsimpl \\ EVAL_TAC)
  \\ xret \\ xsimpl);

val write_list = parse_topdecs
  `fun write_list xs =
     case xs of
         [] => ()
       | x::xs => (CharIO.write x; write_list xs)`;

val _ = ml_prog_update (ml_progLib.add_prog write_list pick_name);

val write_list_spec = Q.store_thm ("write_list_spec",
  `!xs cv output.
     LIST_TYPE WORD xs cv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "write_list" (basis_st()))
       [cv]
       (STDOUT output)
       (POSTv uv. STDOUT (output ++ xs))`,
  Induct
  THEN1
   (xcf "write_list" (basis_st()) \\ fs [LIST_TYPE_def]
    \\ xmatch \\ xcon \\ xsimpl)
  \\ fs [LIST_TYPE_def,PULL_EXISTS] \\ rw []
  \\ xcf "write_list" (basis_st()) \\ fs [LIST_TYPE_def]
  \\ xmatch
  \\ xlet `POSTv uv. STDOUT (output ++ [h])`
  THEN1
   (xapp \\ instantiate
    \\ qexists_tac `emp` \\ qexists_tac `output` \\ xsimpl)
  \\ xapp \\ xsimpl
  \\ qexists_tac `emp`
  \\ qexists_tac `output ++ [h]`
  \\ xsimpl \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ xsimpl);

fun apply_normalise tm =
  if type_of tm = astSyntax.exp_ty
  then rhs(concl(EVAL``full_normalise [] ^tm``))
  else
  (let val (a,d) = dest_comb tm in
     mk_comb(apply_normalise a, apply_normalise d)
   end handle HOL_ERR _ => tm)

val normalise_topdecs = apply_normalise o parse_topdecs

val read_all = normalise_topdecs
  `fun read_all cs =
    let
      val u = ()
      val c = CharIO.read u
    in
      if CharIO.read_failed u then
        reverse cs
      else
        read_all (c::cs)
      end`;

val _ = ml_prog_update (ml_progLib.add_prog read_all pick_name);

val char_reverse_v_thm = save_thm("char_reverse_v_thm",
  std_preludeTheory.reverse_v_thm
  |> GEN_ALL |> ISPEC ``CHAR``);

val read_all_spec = Q.store_thm ("read_all_spec",
  `!xs cv input read_failed.
     LIST_TYPE CHAR xs cv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "read_all" (basis_st()))
       [cv]
       (STDIN input read_failed)
       (POSTv uv. STDIN "" T * &(LIST_TYPE CHAR (REVERSE xs ++ input) uv))`,
  Induct_on `input`
  THEN1
   (xcf "read_all" (basis_st()) \\ fs [LIST_TYPE_def]
    \\ xlet `POSTv uv. STDIN "" read_failed * &(UNIT_TYPE () uv)`
    THEN1 (xcon \\ fs [] \\ xsimpl)
    \\ xlet `POSTv xv. STDIN "" T` (* TODO: change xv to _ and it breaks the xapp below. what is this bug!? *)
    THEN1
     (xapp \\ fs [PULL_EXISTS] \\ xsimpl
      \\ qexists_tac `emp`
      \\ qexists_tac`read_failed`
      \\ qexists_tac `""` \\ xsimpl)
    \\ xlet `POSTv bv. STDIN "" T * cond (BOOL T bv)`
    >- ( xapp \\ fs[] )
    \\ xif \\ instantiate
    \\ xapp
    \\ xsimpl
    \\ instantiate)
  \\ xcf "read_all" (basis_st()) \\ fs [LIST_TYPE_def]
  \\ xlet `POSTv v. STDIN (STRING h input) read_failed * &(UNIT_TYPE () v)`
  >- (xcon \\ xsimpl )
  \\ xlet `POSTv v. STDIN input F * &(CHAR h v)`
  >- (
    xapp
    \\ fs[PULL_EXISTS]
    \\ qexists_tac`emp`
    \\ qexists_tac`read_failed`
    \\ qexists_tac`h::input`
    \\ xsimpl )
  \\ xlet `POSTv v. STDIN input F * &(BOOL F v)`
  >- ( xapp \\ fs[] )
  \\ xif \\ instantiate
  \\ xlet `POSTv x. STDIN input F * &(LIST_TYPE CHAR (h::xs) x)`
  THEN1 (xcon \\ xsimpl \\ fs [LIST_TYPE_def])
  \\ xapp
  \\ instantiate \\ xsimpl
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ qexists_tac`emp`
  \\ qexists_tac`F`
  \\ xsimpl);

(* --- the following are defs and lemmas used by ioProgLib --- *)

val io_ffi_oracle_def = Define `
  (io_ffi_oracle:(string # (word8 list)) oracle) =
    \name (inp,out) bytes.
       if name = "putChar" then
         case bytes of
         | [b] => Oracle_return (inp,out ++ [b]) [b]
         | _ => Oracle_fail
       else if name = "getChar" then
         case bytes of
         | [b;f] =>
           if inp = "" then
             Oracle_return (inp,out) [b; 1w]
           else
             Oracle_return (TL inp,out) [n2w(ORD(HD inp)); 0w]
         | _ => Oracle_fail
       else Oracle_fail`

val io_ffi_def = Define `
  io_ffi (inp:string) =
    <| oracle := io_ffi_oracle
     ; ffi_state := (inp,[])
     ; final_event := NONE
     ; io_events := [] |>`;

val io_proj1_def = Define `
  io_proj1 = (\(inp,out:word8 list).
    FEMPTY |++ [("putChar",Str (MAP (CHR o w2n) out));("getChar",Str inp)])`;

val io_proj2_def = Define `
  io_proj2 = [(["putChar"],stdout_fun);(["getChar"],stdin_fun)]`;

val extract_output_def = Define `
  (extract_output [] = SOME []) /\
  (extract_output ((IO_event name bytes)::xs) =
     case extract_output xs of
     | NONE => NONE
     | SOME rest =>
         if name <> "putChar" then SOME rest else
         if LENGTH bytes <> 1 then NONE else
           SOME ((SND (HD bytes)) :: rest))`

val extract_output_APPEND = Q.store_thm("extract_output_APPEND",
  `!xs ys.
      extract_output (xs ++ ys) =
      case extract_output ys of
      | NONE => NONE
      | SOME rest => case extract_output xs of
                     | NONE => NONE
                     | SOME front => SOME (front ++ rest)`,
  Induct \\ fs [APPEND,extract_output_def] \\ rw []
  THEN1 (every_case_tac \\ fs [])
  \\ Cases_on `h` \\ fs [extract_output_def]
  \\ rpt (CASE_TAC \\ fs []));

val evaluate_prog_RTC_call_FFI_rel = Q.store_thm("evaluate_prog_RTC_call_FFI_rel",
  `evaluate_prog F env st prog (st',tds,res) ==>
    RTC call_FFI_rel st.ffi st'.ffi`,
  rw[bigClockTheory.prog_clocked_unclocked_equiv]
  \\ (funBigStepEquivTheory.functional_evaluate_tops
      |> CONV_RULE(LAND_CONV SYM_CONV) |> LET_INTRO
      |> Q.GENL[`tops`,`s`,`env`]
      |> qspecl_then[`env`,`st with clock := c`,`prog`]mp_tac)
  \\ rw[] \\ pairarg_tac \\ fs[]
  \\ drule evaluatePropsTheory.evaluate_tops_call_FFI_rel_imp
  \\ imp_res_tac determTheory.prog_determ
  \\ fs[] \\ rw[]);

val RTC_call_FFI_rel_IMP_io_events = Q.store_thm("RTC_call_FFI_rel_IMP_io_events",
  `!st st'.
      call_FFI_rel^* st st' ==>
      st.oracle = io_ffi_oracle /\
      extract_output st.io_events = SOME (SND (st.ffi_state)) ==>
      extract_output st'.io_events = SOME (SND (st'.ffi_state))`,
  HO_MATCH_MP_TAC RTC_INDUCT \\ rw [] \\ fs []
  \\ fs [evaluatePropsTheory.call_FFI_rel_def]
  \\ fs [ffiTheory.call_FFI_def]
  \\ Cases_on `st.final_event = NONE` \\ fs [] \\ rw []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ Cases_on `f` \\ fs []
  \\ reverse (Cases_on `n = "putChar"`) \\ fs []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ fs [extract_output_APPEND,extract_output_def] \\ rfs []
  THEN1
   (fs [io_ffi_oracle_def]
    \\ fs [] \\ Cases_on `st.ffi_state` \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [])
  \\ every_case_tac \\ fs []
  THEN1
   (fs [io_ffi_oracle_def]
    \\ fs [] \\ Cases_on `st.ffi_state` \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [])
  \\ Cases_on `bytes` \\ fs [] \\ Cases_on `l` \\ fs []
  \\ Cases_on `t` \\ fs [] \\ Cases_on `t'` \\ fs []
  \\ fs [io_ffi_oracle_def]
  \\ Cases_on `st.ffi_state` \\ fs [] \\ rw []);

val MAP_CHR_w2n_11 = Q.store_thm("MAP_CHR_w2n_11",
  `!ws1 ws2:word8 list.
      MAP (CHR ∘ w2n) ws1 = MAP (CHR ∘ w2n) ws2 <=> ws1 = ws2`,
  Induct \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `ws2` \\ fs [] \\ metis_tac [CHR_11,w2n_lt_256,w2n_11]);

val evaluate_prog_rel_IMP_evaluate_prog_fun = Q.store_thm(
   "evaluate_prog_rel_IMP_evaluate_prog_fun",
  `bigStep$evaluate_whole_prog F env st prog (st',new_tds,Rval r) ==>
    ?k. evaluate$evaluate_prog (st with clock := k) env prog =
          (st',new_tds,Rval r)`,
  rw[bigClockTheory.prog_clocked_unclocked_equiv,bigStepTheory.evaluate_whole_prog_def]
  \\ qexists_tac`c + st.clock`
  \\ (funBigStepEquivTheory.functional_evaluate_prog
      |> CONV_RULE(LAND_CONV SYM_CONV) |> LET_INTRO |> GEN_ALL
      |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s","env","prog"]))
      |> qspecl_then[`st with clock := c + st.clock`,`env`,`prog`]mp_tac)
  \\ rw[] \\ pairarg_tac \\ fs[]
  \\ fs[bigStepTheory.evaluate_whole_prog_def]
  \\ drule bigClockTheory.prog_add_to_counter \\ simp[]
  \\ disch_then(qspec_then`st.clock`strip_assume_tac)
  \\ drule determTheory.prog_determ
  \\ every_case_tac \\ fs[]
  \\ TRY (disch_then drule \\ rw[])
  \\ fs[semanticPrimitivesTheory.state_component_equality]);

val parts_ok_io_ffi = Q.store_thm("parts_ok_io_ffi",
  `parts_ok (io_ffi input) (io_proj1,io_proj2)`,
  fs [cfStoreTheory.parts_ok_def]
  \\ rw [] \\ TRY (EVAL_TAC \\ NO_TAC)
  THEN1
   (fs [io_proj2_def,io_proj1_def,io_ffi_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
    \\ EVAL_TAC \\ qexists_tac `Str input` \\ fs [] \\ rw [])
  THEN1
   (fs [io_proj2_def] \\ rveq \\ fs [stdout_fun_def,stdin_fun_def]
    \\ rfs [io_proj1_def] \\ pairarg_tac \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
  THEN1
   (fs [io_ffi_def,io_ffi_oracle_def,io_proj2_def] \\ rveq \\ fs []
    \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
    \\ every_case_tac \\ fs [stdout_fun_def,stdin_fun_def,io_proj1_def]
    \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
    \\ rveq \\ fs [GSYM fmap_EQ,FUN_EQ_THM]
    \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
    \\ rw [] \\ fs [] \\ rfs[]));

val _ = export_theory ()
