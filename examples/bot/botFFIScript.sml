(*
  The botFFI interface
*)

open preamble cfHeapsBaseTheory
open MonitorProgTheory

val _ = new_theory"botFFI"

(*
  This is our logical FFI state machine model for the control/plant model
  However, we have included everything into the mach model

  The model has three parts:
   - The mach_config is an immutable configuration for the mach.
   - The mach_state is unknown, and gets seen by the FFI
   - The mach_oracle gives the oracle transitions
*)

val _ = Datatype`
  mach_config = <|
    const_names        : string list;
    sensor_names       : string list;
    sensorplus_names   : string list;
    ctrl_names         : string list;
    ctrlplus_names     : string list;
    init               : fml;
    ctrl_monitor       : fml;
    plant_monitor      : fml;
    ctrlfixed_names    : string list;
    ctrlfixed_rhs      : string list;
    default            : trm list
  |>`

val _ = Datatype`
  mach_state = <|
    const_vals   : word32 list; (* Fixed constants *)
    ctrl_vals    : word32 list; (* Current values of ctrl *)
    sensor_vals  : word32 list; (* Current values of sensors *)
    |>`

val _ = Datatype`
  mach_oracle = <|
    (* Returns the next control decision when given some input words *)
    ctrl_oracle   : num -> word32 list -> word32 list;
    (* Returns the new observable sensor values when given the current
       mach state and control decision *)
    transition_oracle : num -> (mach_state # word32 list) -> word32 list;
    (* Returns whether we should stop the loop *)
    stop_oracle   : num -> bool;
  |>`

(* a mach is a record of the three components above *)
val _ = Datatype`
  mach = <| wc : mach_config ;
            ws : mach_state  ;
            wo : mach_oracle |>`

(* flatten 4 tuples *)
val FLAT_TUP_def = Define`
  (FLAT_TUP [] = []) ∧
  (FLAT_TUP ((b0,b1,b2,b3)::bs) = [b0;b1;b2;b3]++FLAT_TUP bs)`

(* Consume a list 4 elements at a time *)
val MAP4_def = Define`
  (MAP4 f (a::b::c::d::ls) = f a b c d :: MAP4 f ls) ∧
  (MAP4 f ls = [])`

val w32_to_w8_def = Define`
  w32_to_w8 ls = FLAT_TUP (MAP w32_to_le_bytes ls)`

val w8_to_w32_def = Define`
  w8_to_w32 ls = MAP4 le_bytes_to_w32 ls`

val get_oracle_def = Define`
  get_oracle f = (f 0n,λn. f (n+1))`

(* Specification of the const FFI *)
val ffi_const_def = Define`
  ffi_const (conf:word8 list) (bytes:word8 list) (st:mach) =
  if LENGTH bytes = 4 * LENGTH st.wc.const_names ∧
     (* This second check is added for parts_ok *)
     LENGTH st.wc.const_names = LENGTH st.ws.const_vals
  then
    SOME (FFIreturn (w32_to_w8 st.ws.const_vals) st)
  else
    NONE`

(* Specification of the ctrl FFI *)
val ffi_ctrl_def = Define`
  ffi_ctrl (conf:word8 list) (bytes:word8 list) (st:mach) =
  if LENGTH bytes = 4 * LENGTH st.wc.ctrl_names ∧
     (* This second check is added for parts_ok *)
     LENGTH st.wc.ctrl_names = LENGTH st.ws.ctrl_vals
  then
    SOME (FFIreturn (w32_to_w8 st.ws.ctrl_vals) st)
  else
    NONE`

(* Specification of the sense FFI *)
val ffi_sense_def = Define`
  ffi_sense (conf:word8 list) (bytes:word8 list) (st:mach) =
  if LENGTH bytes = 4 * LENGTH st.wc.sensor_names ∧
     LENGTH st.wc.sensor_names = LENGTH st.ws.sensor_vals
  then
    SOME (FFIreturn (w32_to_w8 st.ws.sensor_vals) st)
  else
    NONE`

(* Specification of the extCtrl FFI *)
val ffi_extCtrl_def = Define`
  ffi_extCtrl (conf:word8 list) (bytes:word8 list) (st:mach) =
  if LENGTH conf = 4 * (LENGTH st.wc.const_names + LENGTH st.wc.sensor_names) ∧
     LENGTH bytes = 4 * LENGTH st.wc.ctrl_names
  then
    let w32s = w8_to_w32 bytes in
    let wo = st.wo in
    let (cur_oracle,next_oracle) = get_oracle wo.ctrl_oracle in
    let w8s = w32_to_w8 (cur_oracle w32s) in
    let new_wo = wo with ctrl_oracle := next_oracle in
    if LENGTH w8s = LENGTH bytes
    then
      SOME (FFIreturn w8s (st with wo := new_wo))
    else
      NONE
  else NONE`

(* Specification of the actuate FFI *)
val ffi_actuate_def = Define`
  ffi_actuate (conf:word8 list) (bytes:word8 list) (st:mach) =
  if LENGTH bytes = 4 * (LENGTH st.wc.ctrl_names)
  then
    let ws = st.ws in
    let wo = st.wo in
    let ctrl = w8_to_w32 bytes in
    let (cur_transition_oracle,next_transition_oracle) = get_oracle wo.transition_oracle in
    let (cur_stop_oracle,next_stop_oracle) = get_oracle wo.stop_oracle in
    if ¬cur_stop_oracle
    then
      (* Transition to the new mach state *)
      let new_ws = ws with <|sensor_vals := cur_transition_oracle (ws,ctrl); ctrl_vals := ctrl|> in
      let new_wo = wo with <|transition_oracle := next_transition_oracle;
                             stop_oracle       := next_stop_oracle|> in
        SOME (FFIreturn bytes (st with <|wo := new_wo ; ws := new_ws |>))
    else
       NONE
  else NONE`

(* Specification of the stop FFI *)
val ffi_stop_def = Define`
  ffi_stop (conf:word8 list) (bytes:word8 list) (st:mach) =
  if LENGTH bytes = 1
  then
    if st.wo.stop_oracle 0 then
      SOME (FFIreturn [1w:word8] st)
    else
      SOME (FFIreturn [0w:word8]st)
  else
    NONE`

(* Specification of the violation FFI *)
val ffi_violation_def = Define`
  ffi_violation (conf:word8 list) (bytes:word8 list) (st:mach) =
  if LENGTH bytes = 0
  then
    SOME (FFIreturn bytes st)
  else
    NONE`

val comp_eq = map theorem ["mach_component_equality",
                           "mach_config_component_equality",
                           "mach_state_component_equality",
                           "mach_oracle_component_equality"];

(* This section defines an encoding of the mach into CakeML's 'ffi type *)

(* Turn a word32 list into a list of strings invertibly *)
Theorem w2sCHR_11:
  w2s 2 CHR c = w2s 2 CHR c' ⇒ c = c'
Proof
  rw[]>>
  qsuff_tac `∀h. s2w 2 ORD (w2s 2 CHR h) = h` >>fs[]
  >-
    metis_tac[]
  >>
    rw[]>>match_mp_tac s2w_w2s>>simp[]
QED

val encode_word32_list_def = Define`
  encode_word32_list = encode_list (Str o w2s 2 CHR)`

Theorem encode_word32_list_11:
  !x y. encode_word32_list x = encode_word32_list y <=> x = y
Proof
  Induct \\ Cases_on `y`
  \\ fs [encode_word32_list_def,encode_list_def]
  \\ metis_tac[w2sCHR_11]
QED

val decode_encode_word32_list = new_specification("decode_encode_word32_list",["decode_word32_list"],
  prove(``?decode_word32_list. !cls. decode_word32_list (encode_word32_list cls) = SOME cls``,
        qexists_tac `\f. some c. encode_word32_list c = f` \\ fs [encode_word32_list_11]));
val _ = export_rewrites ["decode_encode_word32_list"];

val encode_trm_def = Define`
  (encode_trm (Const w) = Cons (Num 0) (Str (w2s 2 CHR w))) ∧
  (encode_trm (Var s) = Cons (Num 1) (Str s)) ∧
  (encode_trm (Plus t1 t2) = Cons (Num 2) (Cons (encode_trm t1) (encode_trm t2))) ∧
  (encode_trm (Times t1 t2) = Cons (Num 3) (Cons (encode_trm t1) (encode_trm t2))) ∧
  (encode_trm (Div t1 t2) = Cons (Num 4) (Cons (encode_trm t1) (encode_trm t2))) ∧
  (encode_trm (Max t1 t2) = Cons (Num 5) (Cons (encode_trm t1) (encode_trm t2))) ∧
  (encode_trm (Min t1 t2) = Cons (Num 6) (Cons (encode_trm t1) (encode_trm t2))) ∧
  (encode_trm (Neg t) = Cons (Num 7) (encode_trm t)) ∧
  (encode_trm (Abs t) = Cons (Num 8) (encode_trm t))`

Theorem encode_trm_11:
  ∀x y. encode_trm x = encode_trm y <=> x = y
Proof
  Induct>>Cases_on`y`>>rw[encode_trm_def]>>
  fs[mlstringTheory.explode_11]>>
  metis_tac[w2sCHR_11]
QED

val decode_encode_trm = new_specification("decode_encode_trm",["decode_trm"],
  prove(``?decode_trm. !cls. decode_trm (encode_trm cls) = SOME cls``,
        qexists_tac `\f. some c. encode_trm c = f` \\ fs [encode_trm_11]));
val _ = export_rewrites ["decode_encode_trm"];

val encode_fml_def = Define`
  (encode_fml (Le t1 t2) = Cons (Num 0) (Cons (encode_trm t1) (encode_trm t2))) ∧
  (encode_fml (Leq t1 t2) = Cons (Num 1) (Cons (encode_trm t1) (encode_trm t2))) ∧
  (encode_fml (Equals t1 t2) = Cons (Num 2) (Cons (encode_trm t1) (encode_trm t2))) ∧
  (encode_fml (And f1 f2) = Cons (Num 3) (Cons (encode_fml f1) (encode_fml f2))) ∧
  (encode_fml (Or f1 f2) = Cons (Num 4) (Cons (encode_fml f1) (encode_fml f2))) ∧
  (encode_fml (Not f) = Cons (Num 5) (encode_fml f))`

Theorem encode_fml_11:
  ∀x y. encode_fml x = encode_fml y <=> x = y
Proof
  Induct>>Cases_on`y`>>rw[encode_fml_def]>>
  metis_tac[encode_trm_11]
QED

val decode_encode_fml = new_specification("decode_encode_fml",["decode_fml"],
  prove(``?decode_fml. !cls. decode_fml (encode_fml cls) = SOME cls``,
        qexists_tac `\f. some c. encode_fml c = f` \\ fs [encode_fml_11]));
val _ = export_rewrites ["decode_encode_fml"];

(* Encode the fixed list *)
val encode_sum_list_def = Define`
  encode_sum_list = encode_list
    (λs. case s of
     INL w =>
       Cons (Num 0) (Str (w2s 2 CHR w))
    | INR x =>
       Cons (Num 1) (Str x))`

Theorem encode_sum_list_11:
  !x y. encode_sum_list x = encode_sum_list y <=> x = y
Proof
  Induct \\ Cases_on `y`
  \\ fs [encode_sum_list_def,encode_list_def]
  \\ rw[]>>every_case_tac>>fs[]
  \\ metis_tac[w2sCHR_11]
QED

val encode_mach_config_def = Define`
  encode_mach_config wc =
   Cons (List (MAP (Str ) wc.const_names))
   (Cons (List (MAP (Str) wc.sensor_names))
   (Cons (List (MAP (Str) wc.sensorplus_names))
   (Cons (List (MAP (Str) wc.ctrl_names))
   (Cons (List (MAP (Str) wc.ctrlplus_names))
   (Cons (encode_fml wc.init)
   (Cons (encode_fml wc.ctrl_monitor)
   (Cons (encode_fml wc.plant_monitor)
   (Cons (List (MAP Str wc.ctrlfixed_names))
   (Cons (List (MAP Str wc.ctrlfixed_rhs))
   (List (MAP encode_trm wc.default))
   )))))))))`

Theorem MAP_Str_11:
  MAP (Str) ls =
  MAP (Str) ls' ==>
  ls = ls'
Proof
  fs[LIST_EQ_REWRITE]>>
  rw[]>>
  rfs[EL_MAP]>>
  metis_tac[]
QED

val encode_default_11 = Q.prove(`
  ∀x y.
  MAP encode_trm x = MAP encode_trm y ⇒ x = y`,
  Induct>>fs[]>>Cases_on`y`>>fs[encode_trm_11]);

val encode_mach_config_11 = Q.prove(`
  encode_mach_config x = encode_mach_config y ⇔
  x = y`,
  fs[encode_mach_config_def]>>
  rw[EQ_IMP_THM]>>fs comp_eq>>
  fs[MAP_Str_11,encode_fml_11,encode_sum_list_11,encode_default_11]);

val encode_word32_list_inner_def = Define`
  encode_word32_list_inner = iList o (MAP (iStr o w2s 2 CHR))`

val encode_mach_state_def = Define`
  encode_mach_state ws =
  Cons (encode_word32_list ws.const_vals)
  (Cons (encode_word32_list ws.ctrl_vals)
  (encode_word32_list ws.sensor_vals))`

(* This is a bit special: we will use the inner type as well *)
val encode_mach_state_inner_def = Define`
  encode_mach_state_inner ws =
  iCons (encode_word32_list_inner ws.const_vals)
  (iCons (encode_word32_list_inner ws.ctrl_vals)
  (encode_word32_list_inner ws.sensor_vals))`

val encode_mach_state_11 = Q.prove(`
  encode_mach_state x = encode_mach_state y ⇔
  x = y`,
  rw[encode_mach_state_def]>>fs comp_eq>>
  metis_tac[encode_word32_list_11]);

val encode_word32_list_inner_11 = Q.prove(`
  !x y. encode_word32_list_inner x = encode_word32_list_inner y <=> x = y`,
  Induct \\ Cases_on `y`
  \\ fs [encode_word32_list_inner_def]
  \\ metis_tac[w2sCHR_11]);

val encode_mach_state_inner_11 = Q.prove(`
  encode_mach_state_inner x =
  encode_mach_state_inner y <=>
  x = y`,
  rw[encode_mach_state_inner_def]>>fs comp_eq>>
  metis_tac[encode_word32_list_inner_11]);

val decode_encode_mach_state_inner = new_specification("decode_encode_mach_state_inner",["decode_mach_state_inner"],
  prove(``?decode. !cls. decode (encode_mach_state_inner cls) = SOME cls``,
        qexists_tac `\f. some c. encode_mach_state_inner c = f` \\ fs [encode_mach_state_inner_11]));
val _ = export_rewrites ["decode_encode_mach_state_inner"];

(* Now we encode the oracles *)
val get_num_def = Define`
  (get_num (iNum n) = n) ∧
  (get_num _ = 0)`

val get_word32_def = Define`
  (get_word32 (iStr s) = (s2w 2 ORD s)) ∧
  (get_word32 _ = 0w:word32)`

val get_word32_list_def = Define`
  (get_word32_list (iList ls) = MAP get_word32 ls) /\
  (get_word32_list _ = [])`

val encode_stop_oracle_def = Define`
  encode_stop_oracle stop_oracle =
    Fun (λnum:ffi_inner.
      Num (if stop_oracle (get_num num) then 1 else 0))`

val encode_stop_oracle_11 = Q.prove(`
  encode_stop_oracle x = encode_stop_oracle y ==>
  x = y`,
  rw[]>>fs[FUN_EQ_THM,encode_stop_oracle_def]>>rw[]>>
  pop_assum(qspec_then`iNum x'` assume_tac)>>fs[get_num_def]>>
  every_case_tac>>fs[]);

val encode_ctrl_oracle_def = Define`
  encode_ctrl_oracle ctrl_oracle =
    Fun (λnum:ffi_inner.
    Fun (λw32ls:ffi_inner.
      encode_word32_list (ctrl_oracle (get_num num) (get_word32_list w32ls))))`

Theorem encode_ctrl_oracle_11:
  encode_ctrl_oracle f = encode_ctrl_oracle f' ⇒
  f = f'
Proof
  rw[encode_ctrl_oracle_def]>>
  fs[FUN_EQ_THM]>>
  rw[]>>
  pop_assum (qspecl_then[`iNum x`,`iList (MAP (iStr o w2s 2 CHR) x')`] assume_tac)>>
  fs[get_num_def,get_word32_list_def,get_word32_def,MAP_MAP_o,o_DEF]>>
  `∀x:word32. s2w 2 ORD (w2s 2 CHR x)= x` by
     (rw[]>>match_mp_tac s2w_w2s>>fs[])>>
  fs[]>>
  metis_tac[encode_word32_list_11]
QED

val get_st_ctrl_pair_def = Define`
  (get_st_ctrl_pair (iCons st ctrl) =
    case decode_mach_state_inner st of
      NONE => ARB
    | SOME st => (st, get_word32_list ctrl)) ∧
  (get_st_ctrl_pair _ = ARB)`

(* This is a bit strange... *)
val encode_transition_oracle_def = Define`
  encode_transition_oracle transition_oracle =
    Fun (λnum:ffi_inner.
    Fun (λstpr:ffi_inner.
    encode_word32_list (transition_oracle (get_num num) (get_st_ctrl_pair stpr))))`

val encode_transition_oracle_11 = Q.prove(`
  encode_transition_oracle f = encode_transition_oracle f' ==>
  f = f'`,
  rw[encode_transition_oracle_def]>>
  fs[FUN_EQ_THM]>>
  rw[]>>
  Cases_on`x'`>>
  pop_assum (qspecl_then[`iNum x`,`iCons (encode_mach_state_inner q) (encode_word32_list_inner r)`] assume_tac)>>
  fs[get_num_def,get_st_ctrl_pair_def,get_word32_list_def,encode_word32_list_inner_def]>>
  fs[MAP_MAP_o,o_DEF,get_word32_def]>>
  `∀x:word32. s2w 2 ORD (w2s 2 CHR x)= x` by
     (rw[]>>match_mp_tac s2w_w2s>>fs[])>>
  fs[]>>
  metis_tac[encode_word32_list_11]);

val encode_mach_oracle_def = Define`
  encode_mach_oracle wo =
  Cons (encode_ctrl_oracle wo.ctrl_oracle)
  (Cons (encode_transition_oracle wo.transition_oracle)
  (encode_stop_oracle wo.stop_oracle))`

val encode_mach_oracle_11 = Q.prove(`
  encode_mach_oracle x = encode_mach_oracle y ⇔
  x = y`,
  fs[encode_mach_oracle_def]>>rw[EQ_IMP_THM]>>
  fs comp_eq>>
  metis_tac[encode_transition_oracle_11,encode_ctrl_oracle_11,encode_stop_oracle_11]);

val encode_def = Define`
  encode w =
   Cons (encode_mach_config w.wc)
  (Cons (encode_mach_state w.ws)
  (encode_mach_oracle w.wo))`

Theorem encode_11:
  ∀w w'.
  encode w' = encode w <=> w' = w
Proof
  fs[encode_def]>>
  rw[EQ_IMP_THM]>>fs comp_eq>>
  fs[encode_mach_config_11,encode_mach_state_11,encode_mach_oracle_11]
QED

val decode_encode = new_specification("decode_encode",["decode"],
  prove(``?decode. !cls. decode (encode cls) = SOME cls``,
        qexists_tac `\f. some c. encode c = f` \\ fs [encode_11]));
val _ = export_rewrites ["decode_encode"];

val bot_ffi_part_def = Define`
  bot_ffi_part =
    (encode,decode,
      [("const",ffi_const);
       ("ctrl",ffi_ctrl);
       ("sense",ffi_sense);
       ("extCtrl",ffi_extCtrl);
       ("actuate",ffi_actuate);
       ("stop",ffi_stop);
       ("violation",ffi_violation);
       ])`;

Theorem LENGTH_w32_to_w8:
  ∀ls. LENGTH (w32_to_w8 ls) = 4* LENGTH ls
Proof
  Induct>>fs[w32_to_w8_def,FLAT_TUP_def,w32_to_le_bytes_def]
QED

(* Needed for parts_ok *)
Theorem bot_ffi_LENGTH:
  (ffi_const conf bytes w = SOME (FFIreturn bytes' w') ⇒ LENGTH bytes' = LENGTH bytes) ∧
  (ffi_ctrl conf bytes w = SOME (FFIreturn bytes' w') ⇒ LENGTH bytes' = LENGTH bytes) ∧
  (ffi_sense conf bytes w = SOME (FFIreturn bytes' w') ⇒ LENGTH bytes' = LENGTH bytes) ∧
  (ffi_extCtrl conf bytes w = SOME (FFIreturn bytes' w') ⇒ LENGTH bytes' = LENGTH bytes) ∧
  (ffi_actuate conf bytes w = SOME (FFIreturn bytes' w') ⇒ LENGTH bytes' = LENGTH bytes) ∧
  (ffi_stop conf bytes w = SOME (FFIreturn bytes' w') ⇒ LENGTH bytes' = LENGTH bytes) ∧
  (ffi_violation conf bytes w = SOME (FFIreturn bytes' w') ⇒ LENGTH bytes' = LENGTH bytes)
Proof
  rw[ffi_const_def,ffi_ctrl_def,ffi_sense_def,ffi_extCtrl_def,ffi_actuate_def,ffi_stop_def,ffi_violation_def]>>
  rpt(pairarg_tac>>fs[])>>rw[]>>
  fs[LENGTH_w32_to_w8]
QED

Theorem bot_ffi_no_ffi_div:
  (ffi_const conf bytes w = SOME FFIdiverge ⇒ F) ∧
  (ffi_ctrl conf bytes w = SOME FFIdiverge ⇒ F) ∧
  (ffi_sense conf bytes w = SOME FFIdiverge ⇒ F) ∧
  (ffi_extCtrl conf bytes w = SOME FFIdiverge ⇒ F) ∧
  (ffi_actuate conf bytes w = SOME FFIdiverge ⇒ F) ∧
  (ffi_stop conf bytes w = SOME FFIdiverge ⇒ F) ∧
  (ffi_violation conf bytes w = SOME FFIdiverge ⇒ F)
Proof
  rw[ffi_const_def,ffi_ctrl_def,ffi_sense_def,ffi_extCtrl_def,ffi_actuate_def,ffi_stop_def,ffi_violation_def]>>
  rpt(pairarg_tac>>fs[])>>rw[]>>
  fs[LENGTH_w32_to_w8]
QED

val _ = export_theory();
