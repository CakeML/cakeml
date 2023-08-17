(*
  Translation and hand coded stubs
*)

open preamble ml_progLib ml_translatorLib;
open blastLib cfTacticsLib;
open Word8ArrayProgTheory ml_translatorTheory basisFunctionsLib;
open intervalArithTheory;
open integer_wordTheory;

val _ = new_theory "MonitorProg";

(*"*)

(* Return to the bivalued logic *)
val cwfsem_bi_val_def = Define`
  cwfsem_bi_val f s =
  case cwfsem f s of
    NONE => F
  | SOME F => F
  | SOME T => T`

(*
  Translation of the monitors into CML
*)

val _ = translation_extends"Word8ArrayProg";

(* val _ = ml_prog_update (open_module "Monitor"); *)

val spec32 = INST_TYPE[alpha|->``:32``]
val spec64= INST_TYPE[alpha|->``:64``]
val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)
val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

val word_msb_rw32 = Q.prove(
  `word_msb (a:word32) ⇔ (a>>>31) <> 0w`,
  rw[word_msb_def,fcpTheory.CART_EQ,word_index,word_lsr_def,fcpTheory.FCP_BETA]
  \\ rw[EQ_IMP_THM]
  >- ( qexists_tac`0` \\ simp[] )
  \\ `i = 0` by decide_tac \\ fs[]);

val word_msb_rw64 = Q.prove(
  `word_msb (a:word64) ⇔ (a>>>63) <> 0w`,
  rw[word_msb_def,fcpTheory.CART_EQ,word_index,word_lsr_def,fcpTheory.FCP_BETA]
  \\ rw[EQ_IMP_THM]
  >- ( qexists_tac`0` \\ simp[] )
  \\ `i = 0` by decide_tac \\ fs[]);

val inlines = SIMP_RULE std_ss [NEG_INF_def,POS_INF_def,sw2sw_w2w,word_msb_rw32,word_msb_rw64,word_mul_def,word_2comp_def, divfloor_def, divceil_def, word_smod_def, word_sdiv_def]

val res = translate (integer_wordTheory.WORD_LTi |> spec32)
val res = translate (integer_wordTheory.WORD_LEi |> spec32)
val res = translate (integer_wordTheory.WORD_LEi |> spec64)
val res = translate lookup_def;
val res = translate (round_to_inf_def |> inlines |> econv);

val res = translate (lookup_var_def |> inlines |> econv);
val res = translate (pl_compute |> inlines |> econv);
val res = translate (pu_compute |> inlines |> econv);
val res = translate (wmin_def |> inlines |> econv);
val res = translate (wmax_def |> inlines |> econv);
val res = translate (wtimes_compute |> inlines |> econv);
val res = translate (tl_def |> inlines |> econv);
val res = translate (tu_def |> inlines |> econv);
val res = translate (wneg_def |> inlines |> econv);
val res = translate (wle_def |> inlines);
val res = translate (wleq_def |> inlines);

val res = translate (divl_def |> inlines |> econv);
val res = translate (divu_def |> inlines |> econv);
val res = translate (divPair_def |> inlines |> econv);

val lem = Q.prove(`
  (wle 0w c ⇒ c ≠ 0w) ∧
  (wle 0w c ∧ wleq c d ⇒ d ≠ 0w) ∧
  (¬wleq c 0w ∧ wleq c d ⇒ c ≠ 0w ∧ d ≠ 0w) ∧
  (¬wleq 0w d ⇒ d ≠ 0w) ∧
  (¬wleq 0w d ∧ wleq c d ⇒ c ≠ 0w)
  `,
  EVAL_TAC>>rw[]>>
  CCONTR_TAC>>fs[]>>
  blastLib.FULL_BBLAST_TAC);

val divpair_side = Q.prove(`
  divpair_side a b c d ⇔ T`,
  fs(map (fetch "-") ["divpair_side_def","divu_side_def","divl_side_def"])>>
  rw[w2i_eq_0,lem]>>
  imp_res_tac lem)|> update_precondition;

val res = translate (cwtsem_def |> inlines);
val res = translate (cwfsem_def|>inlines);
val res = translate (cwfsem_bi_val_def|>inlines);

(* The rest of these are wrappers around the monitors *)

(* Converts 4 bytes in little endian order into a 32bit word *)
val le_bytes_to_w32_def = Define`
  le_bytes_to_w32 (b0:word8) (b1:word8) (b2:word8) (b3:word8) =
  (w2w b3):word32 << 24 + (w2w b2) << 16 + (w2w b1) << 8 + (w2w b0)`

(* Converts 32bit word into 4 bytes in little endian order *)
val w32_to_le_bytes_def = Define`
  w32_to_le_bytes (w:word32) =
  ((7 >< 0) w, (15 >< 8) w, (23 >< 16) w, (31 >< 24) w):(word8# word8 # word8 #word8)`

val res = translate (le_bytes_to_w32_def)
val res = translate (w32_to_le_bytes_def |> SIMP_RULE std_ss [word_extract_w2w_mask] |> gconv)

(* Functions for packing and unpacking word32 lists into byte arrays
   and vice versa *)
val pack_w32_list = process_topdecs
  `fun pack_w32_list l =
    let fun f arr l i =
       case l of
          [] => arr
        | (w::ws) =>
        (case w32_to_le_bytes w of
        (b0,bs) =>
        case bs of (b1,bs) =>
        case bs of (b2,b3) =>
        (Word8Array.update arr i b0;
        Word8Array.update arr (i+1) b1;
        Word8Array.update arr (i+2) b2;
        Word8Array.update arr (i+3) b3;
        f arr ws (i + 4)))
    in
      f (Word8Array.array (4 * List.length l) (Word8.fromInt 0)) l 0
    end`;

val _ = append_prog pack_w32_list;

val unpack_w32_list = process_topdecs
  `fun unpack_w32_list arr =
    let fun f arr i lim =
       if i + 4 <= lim then
         (le_bytes_to_w32
         (Word8Array.sub arr i)
         (Word8Array.sub arr (i+1))
         (Word8Array.sub arr (i+2))
         (Word8Array.sub arr (i+3)))::(f arr (i+4) lim)
       else
         []
    in
      f arr 0 (Word8Array.length arr)
    end;`

val _ = append_prog unpack_w32_list

(* Helper function to handoff a state to the monitor *)

(*
val vars_to_state_aux_def = Define`
  (vars_to_state_aux [] [] = []:wstate) ∧
  (vars_to_state_aux (x::xs) (v:word32::vs) = ((x, (v,v))::vars_to_state_aux xs vs)) ∧
  (vars_to_state_aux [] _ = []) ∧
  (vars_to_state_aux _ [] = [])`

val vars_to_state_def = Define`
  vars_to_state xs ys = ZIP (xs,ys)`

val res = translate vars_to_state_aux_def;
val res = translate vars_to_state_def;
*)

(* Now we define the various monitoring wrappers *)

val to_string = process_topdecs`
  fun to_string arr = Word8Array.substring arr 0 (Word8Array.length arr);`

val _ = append_prog to_string;

(* Reads the constants and returns it as a list *)
val const = process_topdecs`
  fun const const_names =
  let val const_vals = Word8Array.array (4 * List.length const_names) (Word8.fromInt 0)
      val u = #(const) "" const_vals
  in
    unpack_w32_list const_vals
  end;`

val _ = append_prog const;

(* Same but for controls (reads the current actuated controls) *)
val ctrl = process_topdecs`
  fun ctrl ctrl_names =
  let val ctrl_vals = Word8Array.array (4 * List.length ctrl_names) (Word8.fromInt 0)
      val u = #(ctrl) "" ctrl_vals
  in
    unpack_w32_list ctrl_vals
  end;`

val _ = append_prog ctrl;

(* Same but for sensors *)
val sense = process_topdecs`
  fun sense sensor_names =
  let val sensor_vals = Word8Array.array (4 * List.length sensor_names) (Word8.fromInt 0)
      val u = #(sense) "" sensor_vals
  in
    unpack_w32_list sensor_vals
  end;`

val _ = append_prog sense;

(* Read the external controls *)
val extCtrl = process_topdecs`
  fun extCtrl ctrl_names const_ls sensor_ls =
  let val csarr = pack_w32_list (const_ls @ sensor_ls)
      val param_str = to_string csarr
      val ctrl_vals = Word8Array.array (4 * List.length ctrl_names) (Word8.fromInt 0)
      val u = #(extCtrl) param_str ctrl_vals
  in
    unpack_w32_list ctrl_vals
  end;`

val _ = append_prog extCtrl;

(* The fixed controller vars are
   a list of (INL) word constants or (INR) constant/sensor names *)
(*
val lookup_fixed_aux_def = Define`
  (lookup_fixed_aux nls [] = []:word32 list) ∧
  (lookup_fixed_aux nls (INL w::xs) = w::lookup_fixed_aux nls xs) ∧
  (lookup_fixed_aux nls (INR x::xs) =
    case ALOOKUP nls x of
      NONE => [] (* This should never occur *)
    | SOME v => v :: lookup_fixed_aux nls xs)`;

val res = translate lookup_fixed_aux_def;
*)

val lookup_fixed_def = Define`
  lookup_fixed nls ls =
  MAP (λn. case ALOOKUP nls n of NONE => 0w:word32 | SOME v => v) ls`

val res = translate lookup_fixed_def;

(* TODO: Do these need to be non-infinity? *)
val is_point_def = Define`
  is_point p ⇔
  FST p = SND p`

val _ = translate is_point_def;

(* only allow defaults that produce point intervals *)
val evaluate_default_def = Define`
  evaluate_default names ls default =
  let defaults =
    MAP (λd. cwtsem d (ZIP (names,ZIP(ls,ls)))) default
  in
    if (EVERY is_point defaults)
    then
      SOME (MAP FST defaults)
    else
      NONE`

val _ = translate evaluate_default_def;

(* Pure controller monitor wrapper
   The additional string literal is used for external logging
*)

val ctrl_monitor_def = Define`
  ctrl_monitor ctrl_phi const_names ctrl_names sensor_names ctrlplus_names
                        const_ls    ctrl_ls sensor_ls    ctrlplus_ls
                        ctrlfixed_names ctrlfixed_rhs default =
  let param_names = sensor_names ++ ctrl_names ++ const_names in
  let param_ls = sensor_ls ++ ctrl_ls ++ const_ls in
  let params = ZIP (param_names,param_ls) in
  let ctrlfixed_ls = lookup_fixed params ctrlfixed_rhs in
  let st_ls    = FLAT [ctrlfixed_ls   ; ctrlplus_ls   ; sensor_ls   ; ctrl_ls ; const_ls] in
  let names_ls = FLAT [ctrlfixed_names; ctrlplus_names; sensor_names; ctrl_names ; const_names] in
  if
    cwfsem_bi_val ctrl_phi (ZIP (names_ls,ZIP(st_ls,st_ls)))
  then
    SOME (strlit"OK",ctrlplus_ls)
  else
  let default_opt = evaluate_default param_names param_ls default
  in
    case default_opt of
      NONE => NONE
    | SOME default_ls => SOME (strlit"Control Violation",default_ls)`

val res = translate ctrl_monitor_def;

val actuate = process_topdecs`
  fun actuate str ctrl_ls =
    let val ctrl_vals = pack_w32_list ctrl_ls in
      (#(actuate) str ctrl_vals; ())
    end`

val _ = append_prog actuate;

(* Checks if there is a next transition *)
val stop = process_topdecs`
  fun stop () =
  let val arr = (Word8Array.array 1 (Word8.fromInt 0))
      val u = #(stop) "" arr
  in
    Word8Array.sub arr 0 <> Word8.fromInt 0
  end`

val _ = append_prog stop;

val violation = process_topdecs`
  fun violation str =
  let val arr = (Word8Array.array 0 (Word8.fromInt 0))
  in
    (#(violation) str arr ; ())
  end`

val _ = append_prog violation;

val plant_monitor_def = Define`
  plant_monitor plant_phi const_names sensor_names ctrl_names sensorplus_names
                          const_ls    sensor_ls    ctrl_ls    sensorplus_ls =
  let names_ls = FLAT [sensorplus_names; ctrl_names; sensor_names; const_names] in
  let st_ls    = FLAT [sensorplus_ls   ; ctrl_ls   ; sensor_ls   ; const_ls] in
    cwfsem_bi_val plant_phi (ZIP (names_ls,ZIP(st_ls,st_ls)))`

val res = translate plant_monitor_def;

val init_monitor_def = Define`
  init_monitor init_phi const_names ctrl_names sensor_names
                        const_ls    ctrl_ls    sensor_ls   =
  let names_ls = FLAT [sensor_names; ctrl_names ; const_names] in
  let st_ls    = FLAT [sensor_ls   ; ctrl_ls ; const_ls] in
    cwfsem_bi_val init_phi (ZIP (names_ls,ZIP(st_ls,st_ls)))`

val res = translate init_monitor_def;

val monitor_loop_body = process_topdecs`
  fun monitor_loop_body plant_phi ctrl_phi
                        const_names sensor_names ctrlplus_names ctrl_names sensorplus_names
                        ctrlfixed_names ctrlfixed_rhs default
                        const_ls ctrl_ls sensor_ls =
  (* First, we we will check if there is a next iteration *)
  if stop() then ()
  else
  let val ctrlplus_ls = extCtrl ctrlplus_names const_ls sensor_ls in
  (* Run the controller monitor *)
  case ctrl_monitor ctrl_phi const_names ctrl_names sensor_names ctrlplus_names
                             const_ls    ctrl_ls    sensor_ls    ctrlplus_ls
                      ctrlfixed_names ctrlfixed_rhs default
  of
  (* default controller could overflow *)
    None => violation "Overflow Violation"
  | Some(flg,ctrl_ls) =>
    let
    val u = actuate flg ctrl_ls
    val sensorplus_ls = sense sensor_names
    in
    if plant_monitor plant_phi const_names sensor_names ctrl_names sensorplus_names
                               const_ls    sensor_ls    ctrl_ls    sensorplus_ls
    then
      let val u = Runtime.fullGC()
      in
        monitor_loop_body plant_phi ctrl_phi
                          const_names sensor_names ctrlplus_names ctrl_names sensorplus_names
                          ctrlfixed_names ctrlfixed_rhs default
                          const_ls ctrl_ls sensorplus_ls
      end
    else
      violation "Plant Violation"
    end
  end`

val _ = append_prog monitor_loop_body;

val monitor_loop = process_topdecs`
  fun monitor_loop init_phi plant_phi ctrl_phi
                   const_names sensor_names ctrlplus_names ctrl_names sensorplus_names
                   ctrlfixed_names ctrlfixed_rhs default =
  (* First read the constants and initial state *)
  let val const_ls = const const_names
      val ctrl_ls =  ctrl ctrl_names
      val sensor_ls = sense sensor_names
  in
    if
      init_monitor init_phi const_names ctrl_names sensor_names const_ls ctrl_ls sensor_ls
    then
      monitor_loop_body plant_phi ctrl_phi
                        const_names sensor_names ctrlplus_names ctrl_names sensorplus_names
                        ctrlfixed_names ctrlfixed_rhs default
                        const_ls ctrl_ls sensor_ls
    else
      violation "Init Violation"
  end`

val _ = append_prog monitor_loop;

(* val _ = ml_prog_update (close_module NONE); *)

val _ = export_theory();
