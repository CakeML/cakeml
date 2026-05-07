(*
  The full setup around distrup core
*)
Theory distrup_fullProg
Libs
  preamble basis wordsLib
Ancestors
  distrup_list distrup_arrayProg words cfHeapsBase cv_std byte

val _ = hide_environments true;

val _ = translation_extends "distrup_arrayProg";

(* Unsigned 32-bit number from a 4-byte string *)
Definition string_to_num_def:
  string_to_num s =
  let
    b0 = &ORD (strsub s 0);
    b1 = &ORD (strsub s 1);
    b2 = &ORD (strsub s 2);
    b3 = &ORD (strsub s 3)
  in
    b0 + b1 * 256 + b2 * 65536 + b3 * (16777216:num)
End

val res = translate string_to_num_def;

Theorem string_to_num_pre:
  string_to_num_side s ⇔
  4 ≤ strlen s
Proof
  rw[fetch "-" "string_to_num_side_def"]
QED

val _ = string_to_num_pre |> update_precondition;

(* Array-level helpers *)
Quote add_cakeml:
  fun get_byte arr i = Word8.toInt (Unsafe.w8sub arr i);

  (* Little-endian: read 4 bytes as signed int starting at index i *)
  fun get_int arr i =
    let
      val b3 = get_byte arr (i+3)
      val raw = get_byte arr i +
                get_byte arr (i+1) * 256 +
                get_byte arr (i+2) * 65536 +
                b3 * 16777216
    in
      if b3 >= 128
      then raw - 4294967296
      else raw
    end;

  fun read_ints arr len i =
    if i >= len then [] else get_int arr (i * 4) :: read_ints arr len (i + 1);

  fun get_u64 arr i =
    get_byte arr i +
    get_byte arr (i+1) * 256 +
    get_byte arr (i+2) * 65536 +
    get_byte arr (i+3) * 16777216 +
    get_byte arr (i+4) * 4294967296 +
    get_byte arr (i+5) * 1099511627776 +
    get_byte arr (i+6) * 281474976710656 +
    get_byte arr (i+7) * 72057594037927936;

  fun read_ids arr len i =
    if i >= len then [] else get_u64 arr (i * 8) :: read_ids arr len (i + 1);

  fun ensure_size buf_arr needed =
    if Word8Array.length buf_arr < needed
    then Word8Array.array needed (Word8.fromInt 0)
    else buf_arr;
End

Definition mk_trusted_def:
  mk_trusted b s =
  if b
  then toString (CHR 1) ^ s
  else toString (CHR 0) ^ s
End

val res = translate mk_trusted_def;

(* get_clause and get_hints read from the respective buffers,
  growing them as necessary *)
Quote add_cakeml:
  fun get_clause buf_arr trusted count_str =
    let
      val len = string_to_num count_str
      val arr = ensure_size buf_arr (len * 4)
      val hdr = mk_trusted trusted count_str
      val _ = #(clause) hdr arr
    in
      (arr, Vector.fromList (read_ints arr len 0))
    end;

  fun get_hints buf_arr count_str =
    let
      val len = string_to_num count_str
      val arr = ensure_size buf_arr (len * 8)
      val _ = #(hints) count_str arr
    in
      (arr, read_ids arr len 0)
    end;
End

(* Fully parse a single step *)
Quote add_cakeml:
  fun parse_step step_arr buf_arr =
    let
      val _ = #(step) "" step_arr
      val c = Char.fromByte (Word8Array.sub step_arr 0)
    in
      case c of
        #"a" => (* PRODUCE *)
          let
            val id = get_u64 step_arr 1
            val nb_lits_str = Word8Array.substring step_arr 9 4
            val nb_hints_str = Word8Array.substring step_arr 13 4
            val (buf_arr, cl) = get_clause buf_arr False nb_lits_str
            val (buf_arr, hints) = get_hints buf_arr nb_hints_str
          in
            (buf_arr, Some (Lrup id cl hints))
          end
      | #"i" => (* IMPORT *)
          let
            val id = get_u64 step_arr 1
            val nb_lits_str = Word8Array.substring step_arr 9 4
            val (buf_arr, cl) = get_clause buf_arr True nb_lits_str
          in
            (buf_arr, Some (Import id cl))
          end
      | #"d" => (* DELETE *)
          let
            val nb_hints_str = Word8Array.substring step_arr 1 4
            val (buf_arr, hints) = get_hints buf_arr nb_hints_str
          in
            (buf_arr, Some (Del hints))
          end
      | #"V" => (buf_arr, Some Validateunsat)
      | _ => (buf_arr, None) (* Terminate or unknown *)
    end;
End

Definition pp_distrup_def:
  pp_distrup distrup =
  case distrup of
  | Del ls =>
      «Del: IDs [» ^ concatWith « » (MAP toString ls) ^ «]»
  | Lrup n vc hints =>
      «Lrup: ID » ^ toString n ^
      « Clause [» ^ concatWith « » (MAP toString (toList vc)) ^ «]»^
      « Hints [» ^ concatWith « » (MAP toString hints) ^ «]»
  | Import n vc =>
      «Import: ID » ^ toString n ^
      « Clause [» ^ concatWith « » (MAP toString (toList vc)) ^ «]»
  | ValidateUnsat =>
      «ValidateUnsat»
End

val res = translate pp_distrup_def;

(* Wraps and removes exception handling *)
Quote add_cakeml:
  fun check_top lno instr st =
    (case st of
      None => (None, "")
    | Some (fml, carr, b) =>
        (case check_distrup_arr lno instr fml carr b of
          (fml, carr, b) => (Some (fml, carr, b), ""))
        handle Fail err =>
        (None, err));
End

(* The main loop *)
Quote add_cakeml:

fun do_callback res step_arr =
  let
    val _ = #(callback) res step_arr
  in
    ()
  end

fun loop step_arr buf_arr st lno =
  let
    val (buf_arr, result) = parse_step step_arr buf_arr
  in
    case result of
      None => () (* Terminate: C handles response after cml_main returns *)
    | Some instr =>
        let
          val (st, msg) = check_top lno instr st
        in
          case st of None =>
            (do_callback ("0" ^ msg) step_arr;
            loop step_arr buf_arr st (lno + 1))
          | Some _ =>
            (do_callback ("1" ^ msg) step_arr;
            loop step_arr buf_arr st (lno + 1))
        end
  end;

fun main () =
  let
    val step_arr = Word8Array.array 17 (Word8.fromInt 0)
    val buf_arr = Word8Array.array 0 (Word8.fromInt 0)
    val fml = Array.array 4096 None
    val carr = Word8Array.array 1024 (Word8.fromInt 0)
    val b = Word8.fromInt 1
  in
    loop step_arr buf_arr (Some (fml, carr, b)) 1
  end;

End

val main_call = ``Dlet unknown_loc Pany (App Opapp [Var (Short «main»); Con NONE []]) ``;;

val prog = get_ml_prog_state () |> get_prog;

val prog_tm = ``SNOC ^main_call ^prog`` |> EVAL |> rconc;

Definition distrup_prog_def:
  distrup_prog = ^prog_tm
End

(*----------------------------------------------------------------------*
   FFI model:
    - the state consists of two parts
       + what to wait for as the next C call
       + the list of pending inputs
    - we need to encode and decode this into/from the ‘:ffi’ type
 *----------------------------------------------------------------------*)

Type w8s = “:word8 list”;

(* what to wait for as the next C call *)
Datatype:
  wait_for = Step
           | Produce_clause w8s w8s
           | Produce_hints w8s
           | Produce_callback
           | Import_clause w8s
           | Import_callback
           | Delete_hints w8s
           | Delete_callback
           | Validate_UNSAT_callback
           | Terminate
End

(* each input is one of: *)
Datatype:
  input = Produce w8s w8s w8s
        | Import w8s w8s
        | Delete w8s w8s
        | Validate_UNSAT w8s
End

(* the state of the C code*)
Type state = “:wait_for # input list # w8s”;

(* encoding *)

Definition Bytes_def:
  Bytes (xs:word8 list) = List (MAP (Num o w2n) xs)
End

Definition Int_def:
  Int i = if i < 0 then Cons (Num (Num (ABS i))) (Num 0) else Num (Num i)
End

Definition WaitFor_def:
  WaitFor wf =
    case wf of
    | Step => Str «Step»
    | Produce_clause xs ys => Cons (Str «Produce_clause») (Cons (Bytes xs) (Bytes ys))
    | Produce_hints xs => Cons (Str «Produce_hints») (Bytes xs)
    | Produce_callback => Str «Produce_callback»
    | Import_clause xs => Cons (Str «Import_clause») (Bytes xs)
    | Import_callback => Str «Import_callback»
    | Delete_hints xs => Cons (Str «Delete_hints») (Bytes xs)
    | Delete_callback => Str «Delete_callback»
    | Validate_UNSAT_callback => Str «Validate_UNSAT_callback»
    | Terminate => Str «Terminate»
End

Definition Input_def:
  Input (Produce xs ys zs)  = Cons (Str «Produce»)
                                   (Cons (Bytes xs) (Cons (Bytes ys) (Bytes zs))) ∧
  Input (Import xs ys)      = Cons (Str «Import»)
                                   (Cons (Bytes xs) (Bytes ys)) ∧
  Input (Delete xs ys)      = Cons (Str «Delete»)
                                   (Cons (Bytes xs) (Bytes ys)) ∧
  Input (Validate_UNSAT xs) = Cons (Str «Validate_UNSAT») (Bytes xs)
End

Definition State_def:
  State wait_for inputs term_bytes =
    Cons (WaitFor wait_for)
         (Cons (List (MAP Input inputs))
               (Bytes term_bytes))
End

Theorem Bytes_11:
  Bytes x = Bytes y ⇔ x = y
Proof
  gvs [Bytes_def] \\ eq_tac
  \\ rw [] \\ drule_at Any MAP_EQ_MAP_IMP \\ gvs []
QED

Theorem Int_11:
  Int x = Int y ⇔ x = y
Proof
  gvs [Int_def] \\ eq_tac \\ rw []
  \\ intLib.COOPER_TAC
QED

Theorem Input_11:
  Input x = Input y ⇔ x = y
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ gvs [Input_def,Bytes_11,Int_11]
QED

Theorem WaitFor_11:
  WaitFor x = WaitFor y ⇔ x = y
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ gvs [WaitFor_def,Bytes_11,Int_11]
QED

Theorem State_11:
  State x y z = State x1 y1 z1 ⇒ x = x1 ∧ y = y1 ∧ z = z1
Proof
  fs [State_def] \\ gvs [WaitFor_11]
  \\ rw [] \\ drule_at Any MAP_EQ_MAP_IMP
  \\ gvs [Input_11,Bytes_11]
QED

(* decoding *)

Definition dest_State_def:
  dest_State (x:ffi) = some res. State (FST res) (FST (SND res)) (SND (SND res)) = x
End

Theorem dest_State_State[simp]:
  dest_State (State w inputs tbytes) = SOME (w, inputs, tbytes)
Proof
  rewrite_tac [dest_State_def]
  \\ DEEP_INTRO_TAC optionTheory.some_intro
  \\ reverse $ rw [FORALL_PROD]
  >- irule_at Any EQ_REFL
  \\ rename [‘FST x’] \\ PairCases_on ‘x’ \\ gvs []
  \\ imp_res_tac State_11 \\ fs []
QED

(* next state *)

val imm_arg = “imm_arg:word8 list”
val arr_arg = “arr_arg:word8 list”

Definition write_bytes_def:
  write_bytes [] xs = [] ∧
  write_bytes xs [] = xs ∧
  write_bytes (x::xs) (y::ys) = (y:word8) :: write_bytes xs ys
End

Definition fix_tb_def:
  fix_tb [] = [n2w (ORD #"T")] ∧
  fix_tb (x::xs) =
    if x ∈ {n2w (ORD #"a"); n2w (ORD #"i"); n2w (ORD #"d"); n2w (ORD #"V")} then
      n2w (ORD #"T") :: xs
    else x::xs : word8 list
End

Definition update_step_def:
  update_step ^imm_arg ^arr_arg Step inputs tb =
    (if LENGTH imm_arg ≠ 0 ∨ LENGTH arr_arg ≠ 17 then NONE else
       case inputs of
       | [] => SOME (FFIreturn (write_bytes arr_arg (fix_tb tb))
                               (State Terminate inputs tb))
       | (i::is) =>
         case i of
         | Produce xs ys zs =>
             let res = write_bytes arr_arg (n2w (ORD #"a") :: xs) in
               SOME (FFIreturn res (State (Produce_clause ys zs) is tb))
         | Import xs ys =>
             let res = write_bytes arr_arg (n2w (ORD #"i") :: xs) in
               SOME (FFIreturn res (State (Import_clause ys) is tb))
         | Delete xs ys =>
             let res = write_bytes arr_arg (n2w (ORD #"d") :: xs) in
               SOME (FFIreturn res (State (Delete_hints ys) is tb))
         | Validate_UNSAT xs =>
             let res = write_bytes arr_arg (n2w (ORD #"V") :: xs) in
               SOME (FFIreturn res (State Validate_UNSAT_callback is tb))) ∧
  update_step ^imm_arg ^arr_arg _ _ _ = NONE
End

Definition update_clause_def:
  update_clause ^imm_arg ^arr_arg (Produce_clause ys zs) inputs tb =
    (SOME (FFIreturn (write_bytes arr_arg ys)
                     (State (Produce_hints zs) inputs tb))) ∧
  update_clause ^imm_arg ^arr_arg (Import_clause ys) inputs tb =
    (SOME (FFIreturn (write_bytes arr_arg ys)
                     (State Import_callback inputs tb))) ∧
  update_clause ^imm_arg ^arr_arg _ _ _ = NONE
End

Definition update_hints_def:
  update_hints ^imm_arg ^arr_arg (Produce_hints zs) inputs tb =
    (SOME (FFIreturn (write_bytes arr_arg zs)
                     (State Produce_callback inputs tb))) ∧
  update_hints ^imm_arg ^arr_arg (Delete_hints zs) inputs tb =
    (SOME (FFIreturn (write_bytes arr_arg zs)
                     (State Delete_callback inputs tb))) ∧
  update_hints ^imm_arg ^arr_arg _ _ _ = NONE
End

Definition match_callback_def:
  match_callback c cb =
    (c = #"a" ∧ cb = Produce_callback ∨
     c = #"i" ∧ cb = Import_callback ∨
     c = #"d" ∧ cb = Delete_callback ∨
     c = #"V" ∧ cb = Validate_UNSAT_callback)
End

Definition update_callback_def:
  (update_callback ^imm_arg ^arr_arg cb inputs tb =
    if 0 < LENGTH arr_arg
    then
      let c = CHR (w2n (HD arr_arg)) in
      if match_callback c cb
      then
        SOME (FFIreturn arr_arg (State Step inputs tb))
      else NONE
    else
      NONE)
End

Definition update_def:
  update ffi_name imm_arg arr_arg s =
    case dest_State s of
    | NONE => NONE
    | SOME (wait_for, inputs, tb) =>
        if ffi_name = «step» then
          update_step imm_arg arr_arg wait_for inputs tb
        else if ffi_name = «clause» then
          update_clause imm_arg arr_arg wait_for inputs tb
        else if ffi_name = «hints» then
          update_hints imm_arg arr_arg wait_for inputs tb
        else if ffi_name = «callback» then
          update_callback imm_arg arr_arg wait_for inputs tb
        else NONE
End

(* definition of separation logic assertion CUSTOM_FFI *)

Definition names_def:
  names = [«step»; «clause»; «hints»; «callback»]
End

Definition CUSTOM_FFI_def:
  CUSTOM_FFI wait_for inputs events tb =
    one (FFI_part (State wait_for inputs tb) update names events)
End

(* verification of FFI calling functions *)

Definition is_final_event_def:
  is_final_event event ⇔
    ∃xs. event = IO_event (ExtCall «step») [] xs ∧
         SND (HD xs) ∉  {n2w (ORD #"a"); n2w (ORD #"i"); n2w (ORD #"d"); n2w (ORD #"V")}
End

Theorem LENGTH_write_bytes:
  ∀xs ys. LENGTH (write_bytes xs ys) = LENGTH xs
Proof
  Induct >> Cases_on ‘ys’ >> gvs [write_bytes_def]
QED

Theorem parse_step_NIL:
  LENGTH step_arr = 17 ⇒
  app (p:'ffi ffi_proj) parse_step_v [step_arrv; buf_arrv]
    (CUSTOM_FFI Step [] events tb *
     W8ARRAY step_arrv step_arr)
    (POSTv res.
       SEP_EXISTS step_arr1 final_event.
         CUSTOM_FFI Terminate [] (events ++ [final_event]) tb *
         W8ARRAY step_arrv step_arr1 *
         cond (LENGTH step_arr1 = 17 ∧ is_final_event final_event ∧
               ∃none.
                 OPTION_TYPE INT NONE none ∧
                 res = Conv NONE [buf_arrv; none]))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "-" "parse_step_v_def") >>
  qabbrev_tac ‘final_event = IO_event (ExtCall «step») []
                                      (ZIP (step_arr,
                                            write_bytes step_arr (fix_tb tb)))’ >>
  xlet ‘POSTv res.
    CUSTOM_FFI Terminate [] (events ++ [final_event]) tb *
    W8ARRAY step_arrv (write_bytes step_arr (fix_tb tb))’
  >-
   (xffi >>
    gvs [CUSTOM_FFI_def,implode_def] >>
    xsimpl >>
    qexists_tac ‘emp’ >> xsimpl >>
    irule_at Any SEP_IMP_REFL >>
    conj_tac >- EVAL_TAC >>
    conj_tac >- EVAL_TAC >>
    simp [update_def,update_step_def] >>
    gvs [names_def,SEP_CLAUSES] >>
    xsimpl) >>
  ‘∃c cs. write_bytes step_arr (fix_tb tb) = c::cs ∧
          c ∉ {n2w (ORD #"a"); n2w (ORD #"i"); n2w (ORD #"d"); n2w (ORD #"V")}’ by
    (gvs [LENGTH_EQ_NUM_compute] >>
     Cases_on ‘tb’ >> gvs [fix_tb_def,write_bytes_def] >>
     IF_CASES_TAC >> gvs [write_bytes_def]) >>
  gvs [] >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  gvs [CHAR_def,WORD_def] >>
  Cases_on ‘c’ >> gvs [] >>
  xmatch >>
  gvs [validate_pat_def,pat_typechecks_def,pat_without_Pref_Pas_def,
       semanticPrimitivesTheory.pmatch_def,
       astTheory.pat_bindings_def,
       semanticPrimitivesTheory.lit_same_type_def] >>
  xlet ‘POSTv res. W8ARRAY step_arrv (n2w n::cs) *
           CUSTOM_FFI Terminate [] (events ++ [final_event]) tb *
           cond (OPTION_TYPE INT NONE res)’
  >- (xcon >> gvs [OPTION_TYPE_def] >> xsimpl) >>
  xcon >>
  xsimpl >>
  qexists_tac ‘final_event’ >>
  xsimpl >>
  unabbrev_all_tac >>
  gvs [is_final_event_def] >>
  ‘LENGTH (n2w n::cs) = 17’ by metis_tac [LENGTH_write_bytes] >>
  ‘LENGTH cs = 16’ by fs [] >>
  gvs [LENGTH_EQ_NUM_compute]
QED

Definition bytes_to_num_def:
  bytes_to_num [] = 0 ∧
  bytes_to_num (b::bs) = w2n (b:word8) + 256 * bytes_to_num bs
End

(*
Definition is_unsat_event_def:
  is_unsat_event event ⇔
    ∃xs. event = IO_event (ExtCall «step») [] xs ∧ SND (HD xs) = n2w (ORD #"V")
End

Theorem parse_step_Validate_UNSAT:
  LENGTH step_arr = 17 ⇒
  app (p:'ffi ffi_proj) parse_step_v [step_arrv; buf_arrv]
    (CUSTOM_FFI Step (Validate_UNSAT xs :: inputs) events *
     W8ARRAY step_arrv step_arr)
    (POSTv res.
       SEP_EXISTS step_arr1 unsat_event.
         CUSTOM_FFI Validate_UNSAT_callback inputs (events ++ [unsat_event]) *
         W8ARRAY step_arrv step_arr1 *
         cond (LENGTH step_arr1 = 17 ∧ is_unsat_event unsat_event ∧
               ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME ValidateUnsat) v ∧
                   res = Conv NONE [buf_arrv; v]))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "-" "parse_step_v_def") >>
  qabbrev_tac ‘unsat_event = IO_event (ExtCall «step») [] (ZIP (step_arr,write_bytes step_arr (86w::xs)))’ >>
  xlet ‘POSTv res.
    CUSTOM_FFI Validate_UNSAT_callback inputs (events ++ [unsat_event]) *
    W8ARRAY step_arrv (write_bytes step_arr (n2w (ORD #"V")::xs))’
  >-
   (xffi >>
    gvs [CUSTOM_FFI_def,implode_def] >>
    xsimpl >>
    qexists_tac ‘emp’  >> xsimpl >>
    irule_at Any SEP_IMP_REFL >>
    conj_tac >- EVAL_TAC >>
    conj_tac >- EVAL_TAC >>
    simp [update_def,update_step_def] >>
    gvs [names_def,SEP_CLAUSES] >>
    xsimpl) >>
  Cases_on ‘step_arr’ >> gvs [write_bytes_def] >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  gvs [CHAR_def,WORD_def] >>
  xmatch >>
  xlet ‘POSTv res. CUSTOM_FFI Validate_UNSAT_callback inputs (events ++ [unsat_event]) *
           W8ARRAY step_arrv (86w::write_bytes t xs) *
           cond (DISTRUP_DISTRUP_TYPE ValidateUnsat res)’
  >- (xcon >> gvs [DISTRUP_DISTRUP_TYPE_def] >> xsimpl) >>
  xlet_auto >- (xsimpl >> xcon >> xsimpl) >>
  xcon >>
  xsimpl >>
  gvs [LENGTH_EQ_NUM_compute] >>
  qexists_tac ‘unsat_event’ >>
  xsimpl >>
  unabbrev_all_tac >>
  rewrite_tac [OPTION_TYPE_def] >>
  gvs [is_unsat_event_def] >>
  ‘LENGTH (write_bytes t xs) = 16’ by (rewrite_tac [LENGTH_write_bytes] >> gvs []) >>
  gvs [LENGTH_EQ_NUM_compute]
QED
*)

Theorem get_byte_spec:
  NUM k nv ∧ k < LENGTH xs ⇒
  app (p:'ffi ffi_proj) get_byte_v [arrv; nv]
      (W8ARRAY arrv xs)
      (POSTv res.
        W8ARRAY arrv xs *
        cond (NUM (w2n (EL k xs)) res))
Proof
  rw[]>>
  xcf_with_def (fetch "-" "get_byte_v_def") >>
  xlet_autop>>
  xapp>>
  asm_exists_tac>>xsimpl
QED

Theorem get_u64_spec:
  ∀xs k nv.
    NUM k nv ∧ k + 8 ≤ LENGTH xs ⇒
    app (p:'ffi ffi_proj) get_u64_v [arrv; nv]
        (W8ARRAY arrv xs)
        (POSTv res.
          W8ARRAY arrv xs *
          cond (NUM (bytes_to_num (TAKE 8 (DROP k xs))) res))
Proof
  rw[]>>
  xcf_with_def (fetch "-" "get_u64_v_def") >>
  rpt (xlet_auto >> xsimpl) >>
  xapp>>xsimpl>>
  gvs[NUM_def]>>
  first_x_assum $ irule_at Any>>
  first_x_assum $ irule_at Any>>
  rw[]>>
  `TAKE 8 (DROP k xs) =
    [xs❲k❳;xs❲k+1❳;xs❲k+2❳;xs❲k+3❳;xs❲k+4❳;xs❲k+5❳;xs❲k+6❳;xs❲k+7❳]` by
      (rw[LIST_EQ_REWRITE,EL_TAKE,EL_DROP]>>
      fs[NUMERAL_LESS_THM ])>>
  rw[bytes_to_num_def]>>gvs[LEFT_ADD_DISTRIB,INT_OF_NUM_ADD]
QED

Theorem get_int_spec:
    NUM k nv ∧ k + 4 ≤ LENGTH xs ⇒
    app (p:'ffi ffi_proj) get_int_v [arrv; nv]
        (W8ARRAY arrv xs)
        (POSTv res.
          W8ARRAY arrv xs *
          cond (INT (w2i (word_of_bytes F 0w (TAKE 4 (DROP k xs)) : word32)) res))
Proof
  rw[]>>
  xcf_with_def (fetch "-" "get_int_v_def") >>
  rpt (xlet_auto >> xsimpl) >>
  ‘k ≤ LENGTH xs’ by decide_tac >>
  drule LESS_EQ_LENGTH >>
  strip_tac >> gvs [EL_APPEND2] >>
  ‘∃y1 y2 y3 y4 ts. ys2 = [y1;y2;y3;y4] ++ ts’ by
   (Cases_on ‘ys2’ >> gvs [] >> rpt (Cases_on ‘t’ >> gvs [] >> Cases_on ‘t'’ >> gvs [])) >>
  gvs [DROP_APPEND,GSYM byteTheory.word_of_bytes_le_def] >>
  DEP_REWRITE_TAC [cv_stdTheory.word_of_bytes_le_eq_num_of_bytes] >>
  conj_tac >- EVAL_TAC >>
  Cases_on ‘y1’ >> gvs [] >>
  Cases_on ‘y2’ >> gvs [] >>
  Cases_on ‘y3’ >> gvs [] >>
  Cases_on ‘y4’ >> gvs [] >>
  rename [‘num_of_bytes [n2w n1; n2w n2; n2w n3; n2w n4]’] >>
  qabbrev_tac ‘kk = n1 + (256 * n2 + (65536 * n3 + 16777216 * n4))’ >>
  ‘num_of_bytes [n2w n1; n2w n2; n2w n3; n2w n4] < dimword (:32) ∧
   num_of_bytes [n2w n1; n2w n2; n2w n3; n2w n4] = kk’ by
    simp [num_of_bytes_def,Abbr‘kk’] >>
  fs [] >>
  pop_assum kall_tac >>
  reverse xif >-
   (xvar>>xsimpl>>
    gvs [INT_def,NUM_def] >>
    gvs [integer_wordTheory.w2i_def,word_msb_n2w] >>
    simp [bitTheory.BIT_def,bitTheory.BITS_THM2,DIV_EQ_X] >>
    rw [] >> unabbrev_all_tac >> gvs []) >>
  xapp >> xsimpl >>
  gvs [NUM_def] >> first_x_assum $ irule_at Any >>
  simp [INT_def] >>
  gvs [integer_wordTheory.w2i_def,word_msb_n2w] >>
  simp [bitTheory.BIT_def,bitTheory.BITS_THM2,DIV_EQ_X] >>
  gvs [INT_def,NUM_def] >>
  rw [] >- intLib.COOPER_TAC >>
  qsuff_tac ‘F’ >> fs [] >>
  pop_assum mp_tac >>
  gvs [Abbr‘kk’]
QED

Definition read_ints_def:
  read_ints k xs =
    if k = 0:num then [] else
      w2i (word_of_bytes F 0w (TAKE 4 xs) : word32) :: read_ints (k-1) (DROP 4 xs)
End

(* Produce events
  TODO: can say more about ss2/ss3 *)
Definition is_produce_events_def:
  is_produce_events id cl produce_events ⇔
    ∃xs1 ss2 xs2 ss3 xs3 clen.
      produce_events = [IO_event (ExtCall «step»)   [] xs1;
                        IO_event (ExtCall «clause») ss2 xs2;
                        IO_event (ExtCall «hints»)  ss3 xs3] ∧
      LENGTH xs1 = 17 ∧
      SND (HD xs1) = n2w (ORD #"a") ∧
      id = bytes_to_num (TAKE 8 (DROP 1 (MAP SND xs1))) ∧
      clen = bytes_to_num (TAKE 4 (DROP 9 (MAP SND xs1))) ∧
      clen * 4 ≤ LENGTH xs2 ∧
      cl = Vector (read_ints clen (MAP SND xs2))
End

(* We only need to know a new array with appropriate length is allocated *)
Theorem ensure_size_spec:
  NUM n nv ⇒
  app (p:'ffi ffi_proj) ensure_size_v [arrv; nv]
      (W8ARRAY arrv xs)
      (POSTv arrv'.
        SEP_EXISTS xs'.
          W8ARRAY arrv' xs' *
          &(n ≤ LENGTH xs'))
Proof
  rw[]>>
  xcf_with_def (fetch "-" "ensure_size_v_def") >>
  xlet_autop>>
  xlet_autop>>
  reverse xif>-
    (xvar>>xsimpl)>>
  xlet_autop>>
  xapp>>xsimpl>>
  rpt (first_x_assum (irule_at Any))>>
  simp[]
QED

Theorem CHR_w2n_n2w_ORD_I:
  (CHR ∘ w2n ∘ (n2w:num -> word8) ∘ ORD) = I
Proof
  RW_TAC std_ss [FUN_EQ_THM,o_DEF]>>
  simp[CHR_w2n_n2w_ORD_simp]
QED

Theorem read_ints_spec:
  ∀lv iv.
  NUM len lv ∧
  NUM i iv ∧
  4 * len ≤ LENGTH xs ⇒
  app (p:'ffi ffi_proj) read_ints_v [arrv; lv; iv]
      (W8ARRAY arrv xs)
      (POSTv res.
        W8ARRAY arrv xs *
        & LIST_TYPE INT
        (read_ints (len - i) (DROP (i * 4) xs)) res)
Proof
  completeInduct_on`len - i`>>
  rw[]>>
  xcf_with_def (fetch "-" "read_ints_v_def") >>
  xlet_autop>>
  xif
  >- (
    xcon>>xsimpl>>
    `len - i = 0` by fs[]>>
    simp[Once read_ints_def,LIST_TYPE_def])>>
  xlet_autop>>
  first_x_assum(qspec_then`len - (i+1)` mp_tac)>>
  impl_tac >- fs[]>>
  disch_then (qspecl_then [`len`, `i+1`] mp_tac)>>
  simp[]>>
  disch_then drule_all>>
  rw[]>>
  rpt xlet_autop>>
  xlet_auto>>
  xcon>>xsimpl>>
  simp[Once read_ints_def,LIST_TYPE_def]>>
  fs[DROP_DROP,LEFT_ADD_DISTRIB]
QED

Theorem get_clause_Produce:
  BOOL b bv ∧
  STRING_TYPE s sv ∧
  4 ≤ strlen s ⇒
  app (p:'ffi ffi_proj) get_clause_v [arrv; bv; sv]
      (CUSTOM_FFI (Produce_clause cl hs) inputs events tb *
        W8ARRAY arrv xs)
      (POSTv res.
        SEP_EXISTS arrv' xs' clausev.
        CUSTOM_FFI (Produce_hints hs) inputs
          (events ++ [IO_event (ExtCall «clause»)
            (MAP (n2w o ORD) (explode (mk_trusted b s)))
               (ZIP (xs',write_bytes xs' cl))]) tb *
        W8ARRAY arrv' (write_bytes xs' cl) *
        &(
          4 * string_to_num s ≤ LENGTH xs' ∧
          vcclause_TYPE (Vector (read_ints (string_to_num s) (write_bytes xs' cl))) clausev ∧
          res = Conv NONE [arrv'; clausev]))
Proof
  rw[]>>
  xcf_with_def (fetch "-" "get_clause_v_def") >>
  rpt xlet_autop>>
  rename1`W8ARRAY arrvv xss`>>
  xlet`POSTv res.
        CUSTOM_FFI (Produce_hints hs) inputs
          (events ++ [IO_event (ExtCall «clause»)
            (MAP (n2w o ORD) (explode (mk_trusted b s)))
            (ZIP (xss,write_bytes xss cl))]) tb *
        W8ARRAY arrvv (write_bytes xss cl)`
  >- (
    xffi>>xsimpl>>
    simp[CUSTOM_FFI_def]>>
    (* conf *)
    qexists_tac`MAP (n2w o ORD) (explode (mk_trusted b s))`>>
    (* frame *)
    qexists_tac`emp`>>
    xsimpl>>
    (* state *)
    qmatch_goalsub_abbrev_tac`FFI_part ss`>>
    qexists_tac`ss`>>
    qexists_tac`update`>>
    qexists_tac`names`>>
    qexists_tac`events`>>
    rw[]
    >- EVAL_TAC
    >- gvs[STRING_TYPE_def,MAP_MAP_o,CHR_w2n_n2w_ORD_I]
    >- EVAL_TAC
    >- xsimpl>>
    simp[update_def,Abbr`ss`,update_clause_def]>>
    xsimpl>>rw[])>>
  xlet_auto
  >-(
    xsimpl>>fs[LENGTH_write_bytes]>>
    metis_tac[])>>
  xlet_autop>>
  xcon>>xsimpl>>
  qexists_tac`xss`>>xsimpl
QED

Theorem read_ids_spec:
  ∀lv iv.
  NUM len lv ∧
  NUM i iv ∧
  8 * len ≤ LENGTH xs ⇒
  app (p:'ffi ffi_proj) read_ids_v [arrv; lv; iv]
      (W8ARRAY arrv xs)
      (POSTv res.
        SEP_EXISTS hs.
        W8ARRAY arrv xs *
        & LIST_TYPE NUM hs res)
Proof
  completeInduct_on`len - i`>>
  rw[]>>
  xcf_with_def (fetch "-" "read_ids_v_def") >>
  xlet_autop>>
  xif
  >- (
    xcon>>xsimpl>>
    qexists_tac`[]`>>simp[LIST_TYPE_def])>>
  xlet_autop>>
  first_x_assum(qspec_then`len - (i+1)` mp_tac)>>
  impl_tac >- fs[]>>
  disch_then (qspecl_then [`len`, `i+1`] mp_tac)>>
  simp[]>>
  disch_then drule_all>>
  rw[]>>
  xlet_auto>>
  xlet_autop>>
  xlet_auto>>
  xcon>>xsimpl>>
  metis_tac[LIST_TYPE_def]
QED

Theorem get_hints_Produce:
  STRING_TYPE s sv ∧
  4 ≤ strlen s ⇒
  app (p:'ffi ffi_proj) get_hints_v [arrv; sv]
      (CUSTOM_FFI (Produce_hints hs) inputs events tb *
        W8ARRAY arrv xs)
      (POSTv res.
        SEP_EXISTS arrv' xs' hints hintsv.
        CUSTOM_FFI Produce_callback inputs
          (events ++ [IO_event (ExtCall «hints»)
            (MAP (n2w o ORD) (explode s))
               (ZIP (xs',write_bytes xs' hs))]) tb *
        W8ARRAY arrv' (write_bytes xs' hs) *
        &(
          4 * string_to_num s ≤ LENGTH xs' ∧
          LIST_TYPE NUM hints hintsv ∧
          res = Conv NONE [arrv'; hintsv]))
Proof
  rw[]>>
  xcf_with_def (fetch "-" "get_hints_v_def") >>
  rpt xlet_autop>>
  rename1`W8ARRAY arrvv xss`>>
  xlet`POSTv res.
        CUSTOM_FFI Produce_callback inputs
          (events ++ [IO_event (ExtCall «hints»)
            (MAP (n2w o ORD) (explode s))
            (ZIP (xss,write_bytes xss hs))]) tb *
        W8ARRAY arrvv (write_bytes xss hs)`
  >- (
    xffi>>xsimpl>>
    simp[CUSTOM_FFI_def]>>
    (* conf *)
    qexists_tac`MAP (n2w o ORD) (explode s)`>>
    (* frame *)
    qexists_tac`emp`>>
    xsimpl>>
    (* state *)
    qmatch_goalsub_abbrev_tac`FFI_part ss`>>
    qexists_tac`ss`>>
    qexists_tac`update`>>
    qexists_tac`names`>>
    qexists_tac`events`>>
    rw[]
    >- EVAL_TAC
    >- gvs[STRING_TYPE_def,MAP_MAP_o,CHR_w2n_n2w_ORD_I]
    >- EVAL_TAC
    >- xsimpl>>
    simp[update_def,Abbr`ss`,update_hints_def]>>
    xsimpl>>rw[])>>
  xlet_auto
  >-(
    xsimpl>>fs[LENGTH_write_bytes]>>
    metis_tac[])>>
  xcon>>xsimpl>>
  qexists_tac`xss`>>xsimpl>>
  metis_tac[]
QED

Theorem string_to_num_eq_bytes_to_num:
  LENGTH ls = 4 ⇒
  string_to_num
  (implode (MAP (CHR ∘ w2n) ls)) =
  bytes_to_num ls
Proof
  rw[LENGTH_EQ_NUM_compute]>>
  simp[string_to_num_def,bytes_to_num_def]>>
  simp[strsub_def,implode_def]>>
  DEP_REWRITE_TAC[ORD_CHR_RWT]>>
  rw[w2n_lt_256]
QED

Theorem parse_step_Produce:
  LENGTH step_arr = 17 ⇒
  app (p:'ffi ffi_proj) parse_step_v [step_arrv; buf_arrv]
    (CUSTOM_FFI Step (Produce xs ys zs :: inputs) events tb *
     W8ARRAY buf_arrv buf_arr *
     W8ARRAY step_arrv step_arr)
    (POSTv res.
       SEP_EXISTS step_arr1 buf_arrv buf_arr produce_events cl hs id.
         CUSTOM_FFI Produce_callback inputs (events ++ produce_events) tb *
         W8ARRAY buf_arrv buf_arr *
         W8ARRAY step_arrv step_arr1 *
         cond (LENGTH step_arr1 = 17 ∧ CHR (w2n (HD step_arr1)) = #"a" ∧
               is_produce_events id cl produce_events ∧
               ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME (Lrup id cl hs)) v ∧
                   res = Conv NONE [buf_arrv; v]))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "-" "parse_step_v_def") >>
  qabbrev_tac ‘a1 = write_bytes step_arr (97w::xs)’ >>
  qabbrev_tac ‘event1 = IO_event (ExtCall «step») [] (ZIP (step_arr,a1))’ >>
  xlet ‘POSTv res.
      CUSTOM_FFI (Produce_clause ys zs) inputs (events ++ [event1]) tb *
      W8ARRAY buf_arrv buf_arr *
      W8ARRAY step_arrv a1’
  >-
   (xffi >>
    gvs [CUSTOM_FFI_def,implode_def] >>
    xsimpl >>
    qexists_tac ‘W8ARRAY buf_arrv buf_arr’ >> xsimpl >>
    irule_at Any SEP_IMP_REFL >>
    conj_tac >- EVAL_TAC >>
    conj_tac >- EVAL_TAC >>
    simp [update_def,update_step_def] >>
    gvs [names_def,SEP_CLAUSES] >>
    xsimpl) >>
  Cases_on ‘step_arr’ >> gvs [write_bytes_def,Abbr‘a1’] >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  gvs [CHAR_def,WORD_def] >>
  xmatch >>
  xlet ‘POSTv res.
    W8ARRAY step_arrv (97w::write_bytes t xs) *
    W8ARRAY buf_arrv buf_arr *
    CUSTOM_FFI (Produce_clause ys zs) inputs (events ++ [event1]) tb *
    cond (NUM (bytes_to_num (TAKE 8 (write_bytes t xs))) res)’
  >-
   (xapp >> xsimpl >> gvs [LENGTH_write_bytes]) >>
  xlet_auto >- (xsimpl >> gvs [LENGTH_write_bytes]) >>
  xlet_auto >- (xsimpl >> gvs [LENGTH_write_bytes]) >>
  xlet_auto >- (xcon \\ xsimpl) >>
  qmatch_asmsub_abbrev_tac`STRING_TYPE ss2 sv`>>
  qmatch_asmsub_abbrev_tac`STRING_TYPE ss3 sv1`>>
  xlet ‘POSTv res.
    SEP_EXISTS buf_arrv1 buf_arr1 cl wss2 io2 clausev.
      W8ARRAY step_arrv (97w::write_bytes t xs) *
      W8ARRAY buf_arrv1 buf_arr1 *
      CUSTOM_FFI (Produce_hints zs) inputs (events ++ [event1;
        IO_event (ExtCall «clause») wss2 io2]) tb *
      cond (
        4 * string_to_num ss2 ≤ LENGTH io2 ∧
        vcclause_TYPE (Vector (read_ints (string_to_num ss2) (MAP SND io2))) clausev ∧
        res = Conv NONE [buf_arrv1; clausev])’
  >- (
    xapp>>
    xsimpl>>
    first_x_assum $ irule_at Any>>
    qexists_tac`tb`>>
    qexists_tac`inputs`>>
    qexists_tac`zs`>>
    qexists_tac`events ++ [event1]`>>
    qexists_tac`ys`>>
    qexists_tac`F`>>
    qexists_tac`W8ARRAY step_arrv (97w::write_bytes t xs)`>>
    xsimpl>>
    rw[]
    >- (
      rw[Abbr`ss2`]>>
      DEP_REWRITE_TAC[LENGTH_TAKE,LENGTH_DROP,LENGTH_write_bytes]>>
      gvs[])>>
    simp[]>>
    rename1`(write_bytes aa bb)`>>
    rename1`IO_event _ sss2 _`>>
    qexists_tac`sss2`>> qexists_tac`ZIP (aa,write_bytes aa bb)`>>
    xsimpl>>simp[LENGTH_write_bytes,MAP_ZIP]>>
    qmatch_goalsub_abbrev_tac`_ ++ [_] ++ [A]`>>
    PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
    REWRITE_TAC[APPEND]>>xsimpl)>>
  qmatch_goalsub_abbrev_tac`[event1; event2]`>>
  gvs [] >>
  xmatch >>
  xlet ‘POSTv res.
    SEP_EXISTS buf_arrv1 buf_arr1 hs wss3 io3.
      W8ARRAY step_arrv (97w::write_bytes t xs) *
      W8ARRAY buf_arrv1 buf_arr1 *
      CUSTOM_FFI Produce_callback inputs (events ++ [event1; event2;
        IO_event (ExtCall «hints») wss3 io3]) tb *
      cond (∃v. res = Conv NONE [buf_arrv1; v] ∧
                LIST_TYPE NUM hs v)’
  >- (
    xapp>>
    xsimpl>>
    first_x_assum $ irule_at Any>>
    qexists_tac`tb`>>
    qexists_tac`inputs`>>
    qexists_tac`zs`>>
    qexists_tac`events ++ [event1; event2]`>>
    qexists_tac`W8ARRAY step_arrv (97w::write_bytes t xs)`>>
    xsimpl>>
    rw[]
    >- (
      rw[Abbr`ss3`]>>
      DEP_REWRITE_TAC[LENGTH_TAKE,LENGTH_DROP,LENGTH_write_bytes]>>
      gvs[])>>
    first_x_assum (irule_at Any)>>
    rename1`IO_event _ sss3 io3`>>
    qexists_tac`io3`>>
    qexists_tac`sss3`>>
    PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
    REWRITE_TAC[APPEND]>>xsimpl)>>
  qmatch_goalsub_abbrev_tac`[event1; event2; event3]`>>
  gvs [] >>
  xmatch >>
  xlet_auto >- (xcon >> xsimpl) >>
  xlet_auto >- (xcon >> xsimpl) >>
  xcon >> xsimpl >>
  simp [PULL_EXISTS] >> xsimpl >>
  qexists ‘[event1; event2; event3]’ >> xsimpl >>
  gvs [] >>
  gvs [OPTION_TYPE_def, DISTRUP_DISTRUP_TYPE_def] >>
  first_x_assum $ irule_at Any >>
  first_x_assum $ irule_at Any >>
  simp [GSYM PULL_EXISTS] >>
  conj_tac
  >-
   (‘LENGTH (write_bytes t xs) = 16’ by (rewrite_tac [LENGTH_write_bytes] >> gvs []) >>
    gvs [LENGTH_EQ_NUM_compute]) >>
  qpat_x_assum ‘NUM _ res’ $ irule_at Any >>
  unabbrev_all_tac>>
  gvs [is_produce_events_def,LENGTH_write_bytes,MAP_ZIP] >>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[string_to_num_eq_bytes_to_num]>>
  DEP_REWRITE_TAC[LENGTH_TAKE,LENGTH_DROP,LENGTH_write_bytes]>>
  gvs[]
QED

Theorem do_callback_gen:
  STRING_TYPE res resv ∧
  0 < LENGTH step_arr ∧
  match_callback (CHR (w2n (HD step_arr))) cb ⇒
  app (p:'ffi ffi_proj) do_callback_v [resv; step_arrv]
    (CUSTOM_FFI cb inputs events tb *
     W8ARRAY step_arrv step_arr)
    (POSTv uv.
         CUSTOM_FFI Step inputs (events ++
            [IO_event (ExtCall «callback») (MAP (n2w ∘ ORD) (explode res))
                 (ZIP (step_arr,step_arr))]) tb *
         W8ARRAY step_arrv step_arr)
Proof
  rw[]>>
  xcf_with_def (fetch "-" "do_callback_v_def") >>
  xlet ‘POSTv uv.
      CUSTOM_FFI Step inputs (events ++
            [IO_event (ExtCall «callback») (MAP (n2w ∘ ORD) (explode res))
                 (ZIP (step_arr,step_arr))]) tb *
       W8ARRAY step_arrv step_arr’
  >-
   (xffi >>
    gvs [CUSTOM_FFI_def,implode_def] >>
    xsimpl >>
    qexists_tac`MAP (n2w o ORD) (explode res)`>>
    qexists_tac ‘emp’ >> xsimpl >>
    irule_at Any SEP_IMP_REFL >>
    conj_tac >- EVAL_TAC >>
    conj_tac >-
      gvs[STRING_TYPE_def,MAP_MAP_o,CHR_w2n_n2w_ORD_I,GSYM implode_def]>>
    conj_tac >- EVAL_TAC >>
    simp [update_def,update_callback_def] >>
    gvs [names_def,SEP_CLAUSES] >>
    xsimpl) >>
  xcon>>xsimpl
QED

Theorem do_callback_Produce:
  STRING_TYPE res resv ∧
  LENGTH step_arr = 17 ∧ CHR (w2n (HD step_arr)) = #"a" ⇒
  app (p:'ffi ffi_proj) do_callback_v [resv; step_arrv]
    (CUSTOM_FFI Produce_callback inputs events tb *
     W8ARRAY step_arrv step_arr)
    (POSTv uv.
         CUSTOM_FFI Step inputs (events ++
            [IO_event (ExtCall «callback») (MAP (n2w ∘ ORD) (explode res))
                 (ZIP (step_arr,step_arr))]) tb *
         W8ARRAY step_arrv step_arr)
Proof
  rw[]>>irule do_callback_gen>>fs[match_callback_def]
QED

(* Import events
  TODO: can say more about ss2/ss3 *)
Definition is_import_events_def:
  is_import_events id cl import_events ⇔
    ∃xs1 ss2 xs2 clen.
      import_events = [IO_event (ExtCall «step»)   [] xs1;
                        IO_event (ExtCall «clause») ss2 xs2] ∧
      LENGTH xs1 = 17 ∧
      SND (HD xs1) = n2w (ORD #"i") ∧
      id = bytes_to_num (TAKE 8 (DROP 1 (MAP SND xs1))) ∧
      clen = bytes_to_num (TAKE 4 (DROP 9 (MAP SND xs1))) ∧
      clen * 4 ≤ LENGTH xs2 ∧
      cl = Vector (read_ints clen (MAP SND xs2))
End

Theorem get_clause_Import:
  BOOL b bv ∧
  STRING_TYPE s sv ∧
  4 ≤ strlen s ⇒
  app (p:'ffi ffi_proj) get_clause_v [arrv; bv; sv]
      (CUSTOM_FFI (Import_clause cl) inputs events tb *
        W8ARRAY arrv xs)
      (POSTv res.
        SEP_EXISTS arrv' xs' clausev.
        CUSTOM_FFI Import_callback inputs
          (events ++ [IO_event (ExtCall «clause»)
            (MAP (n2w o ORD) (explode (mk_trusted b s)))
               (ZIP (xs',write_bytes xs' cl))]) tb *
        W8ARRAY arrv' (write_bytes xs' cl) *
        &(
          4 * string_to_num s ≤ LENGTH xs' ∧
          vcclause_TYPE (Vector (read_ints (string_to_num s) (write_bytes xs' cl))) clausev ∧
          res = Conv NONE [arrv'; clausev]))
Proof
  rw[]>>
  xcf_with_def (fetch "-" "get_clause_v_def") >>
  rpt xlet_autop>>
  rename1`W8ARRAY arrvv xss`>>
  xlet`POSTv res.
        CUSTOM_FFI (Import_callback) inputs
          (events ++ [IO_event (ExtCall «clause»)
            (MAP (n2w o ORD) (explode (mk_trusted b s)))
            (ZIP (xss,write_bytes xss cl))]) tb *
        W8ARRAY arrvv (write_bytes xss cl)`
  >- (
    xffi>>xsimpl>>
    simp[CUSTOM_FFI_def]>>
    (* conf *)
    qexists_tac`MAP (n2w o ORD) (explode (mk_trusted b s))`>>
    (* frame *)
    qexists_tac`emp`>>
    xsimpl>>
    (* state *)
    qmatch_goalsub_abbrev_tac`FFI_part ss`>>
    qexists_tac`ss`>>
    qexists_tac`update`>>
    qexists_tac`names`>>
    qexists_tac`events`>>
    rw[]
    >- EVAL_TAC
    >- gvs[STRING_TYPE_def,MAP_MAP_o,CHR_w2n_n2w_ORD_I]
    >- EVAL_TAC
    >- xsimpl>>
    simp[update_def,Abbr`ss`,update_clause_def]>>
    xsimpl>>rw[])>>
  xlet_auto
  >-(
    xsimpl>>fs[LENGTH_write_bytes]>>
    metis_tac[])>>
  xlet_autop>>
  xcon>>xsimpl>>
  qexists_tac`xss`>>xsimpl
QED

Theorem parse_step_Import:
  LENGTH step_arr = 17 ⇒
  app (p:'ffi ffi_proj) parse_step_v [step_arrv; buf_arrv]
    (CUSTOM_FFI Step (Import xs ys :: inputs) events tb *
     W8ARRAY buf_arrv buf_arr *
     W8ARRAY step_arrv step_arr)
    (POSTv res.
       SEP_EXISTS step_arr1 buf_arrv buf_arr import_events cl id.
         CUSTOM_FFI Import_callback inputs (events ++ import_events) tb *
         W8ARRAY buf_arrv buf_arr *
         W8ARRAY step_arrv step_arr1 *
         cond (LENGTH step_arr1 = 17 ∧ CHR (w2n (HD step_arr1)) = #"i" ∧
               is_import_events id cl import_events ∧
               ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME (Import id cl)) v ∧
                   res = Conv NONE [buf_arrv; v]))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "-" "parse_step_v_def") >>
  qabbrev_tac ‘a1 = write_bytes step_arr (105w::xs)’ >>
  qabbrev_tac ‘event1 = IO_event (ExtCall «step») [] (ZIP (step_arr,a1))’ >>
  xlet ‘POSTv res.
      CUSTOM_FFI (Import_clause ys) inputs (events ++ [event1]) tb *
      W8ARRAY buf_arrv buf_arr *
      W8ARRAY step_arrv a1’
  >-
   (xffi >>
    gvs [CUSTOM_FFI_def,implode_def] >>
    xsimpl >>
    qexists_tac ‘W8ARRAY buf_arrv buf_arr’ >> xsimpl >>
    irule_at Any SEP_IMP_REFL >>
    conj_tac >- EVAL_TAC >>
    conj_tac >- EVAL_TAC >>
    simp [update_def,update_step_def] >>
    gvs [names_def,SEP_CLAUSES] >>
    xsimpl) >>
  Cases_on ‘step_arr’ >> gvs [write_bytes_def,Abbr‘a1’] >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  gvs [CHAR_def,WORD_def] >>
  xmatch >>
  xlet ‘POSTv res.
    W8ARRAY step_arrv (105w::write_bytes t xs) *
    W8ARRAY buf_arrv buf_arr *
    CUSTOM_FFI (Import_clause ys) inputs (events ++ [event1]) tb *
    cond (NUM (bytes_to_num (TAKE 8 (write_bytes t xs))) res)’
  >-
   (xapp >> xsimpl >> gvs [LENGTH_write_bytes]) >>
  xlet_auto >- (xsimpl >> gvs [LENGTH_write_bytes]) >>
  xlet_auto >- (xcon \\ xsimpl) >>
  qmatch_asmsub_abbrev_tac`STRING_TYPE ss2 sv`>>
  xlet ‘POSTv res.
    SEP_EXISTS buf_arrv1 buf_arr1 cl wss2 io2 clausev.
      W8ARRAY step_arrv (105w::write_bytes t xs) *
      W8ARRAY buf_arrv1 buf_arr1 *
      CUSTOM_FFI Import_callback inputs (events ++ [event1;
        IO_event (ExtCall «clause») wss2 io2]) tb *
      cond (
        4 * string_to_num ss2 ≤ LENGTH io2 ∧
        vcclause_TYPE (Vector (read_ints (string_to_num ss2) (MAP SND io2))) clausev ∧
        res = Conv NONE [buf_arrv1; clausev])’
  >- (
    xapp>>
    xsimpl>>
    first_x_assum $ irule_at Any>>
    qexists_tac`tb`>>
    qexists_tac`inputs`>>
    qexists_tac`events ++ [event1]`>>
    qexists_tac`ys`>>
    qexists_tac`T`>>
    qexists_tac`W8ARRAY step_arrv (105w::write_bytes t xs)`>>
    xsimpl>>
    rw[]
    >- (
      rw[Abbr`ss2`]>>
      DEP_REWRITE_TAC[LENGTH_TAKE,LENGTH_DROP,LENGTH_write_bytes]>>
      gvs[])>>
    simp[]>>
    rename1`(write_bytes aa bb)`>>
    rename1`IO_event _ sss2 _`>>
    qexists_tac`sss2`>> qexists_tac`ZIP (aa,write_bytes aa bb)`>>
    xsimpl>>simp[LENGTH_write_bytes,MAP_ZIP]>>
    qmatch_goalsub_abbrev_tac`_ ++ [_] ++ [A]`>>
    PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
    REWRITE_TAC[APPEND]>>xsimpl)>>
  qmatch_goalsub_abbrev_tac`[event1; event2]`>>
  gvs [] >>
  xmatch >>
  xlet_auto >- (xcon >> xsimpl) >>
  xlet_auto >- (xcon >> xsimpl) >>
  xcon >> xsimpl >>
  simp [PULL_EXISTS] >> xsimpl >>
  qexists ‘[event1; event2]’ >> xsimpl >>
  gvs [] >>
  gvs [OPTION_TYPE_def, DISTRUP_DISTRUP_TYPE_def] >>
  first_x_assum $ irule_at Any >>
  first_x_assum $ irule_at Any >>
  simp [GSYM PULL_EXISTS] >>
  conj_tac
  >-
   (‘LENGTH (write_bytes t xs) = 16’ by (rewrite_tac [LENGTH_write_bytes] >> gvs []) >>
    gvs [LENGTH_EQ_NUM_compute]) >>
  unabbrev_all_tac>>
  gvs [is_import_events_def,LENGTH_write_bytes,MAP_ZIP] >>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[string_to_num_eq_bytes_to_num]>>
  DEP_REWRITE_TAC[LENGTH_TAKE,LENGTH_DROP,LENGTH_write_bytes]>>
  gvs[]
QED

Theorem do_callback_Import:
  STRING_TYPE res resv ∧
  LENGTH step_arr = 17 ∧ CHR (w2n (HD step_arr)) = #"i" ⇒
  app (p:'ffi ffi_proj) do_callback_v [resv; step_arrv]
    (CUSTOM_FFI Import_callback inputs events tb *
     W8ARRAY step_arrv step_arr)
    (POSTv uv.
         CUSTOM_FFI Step inputs (events ++
            [IO_event (ExtCall «callback») (MAP (n2w ∘ ORD) (explode res))
                 (ZIP (step_arr,step_arr))]) tb *
         W8ARRAY step_arrv step_arr)
Proof
  rw[]>>irule do_callback_gen>>fs[match_callback_def]
QED

(* Delete events
  TODO: can say more about ss2/ss3 *)
Definition is_delete_events_def:
  is_delete_events delete_events ⇔
    ∃xs1 ss2 xs2.
      delete_events = [IO_event (ExtCall «step»)   [] xs1;
                        IO_event (ExtCall «hints») ss2 xs2] ∧
      LENGTH xs1 = 17 ∧
      SND (HD xs1) = n2w (ORD #"d")
End

Theorem get_hints_Delete:
  STRING_TYPE s sv ∧
  4 ≤ strlen s ⇒
  app (p:'ffi ffi_proj) get_hints_v [arrv; sv]
      (CUSTOM_FFI (Delete_hints hs) inputs events tb *
        W8ARRAY arrv xs)
      (POSTv res.
        SEP_EXISTS arrv' xs' hints hintsv.
        CUSTOM_FFI Delete_callback inputs
          (events ++ [IO_event (ExtCall «hints»)
            (MAP (n2w o ORD) (explode s))
               (ZIP (xs',write_bytes xs' hs))]) tb *
        W8ARRAY arrv' (write_bytes xs' hs) *
        &(
          4 * string_to_num s ≤ LENGTH xs' ∧
          LIST_TYPE NUM hints hintsv ∧
          res = Conv NONE [arrv'; hintsv]))
Proof
  rw[]>>
  xcf_with_def (fetch "-" "get_hints_v_def") >>
  rpt xlet_autop>>
  rename1`W8ARRAY arrvv xss`>>
  xlet`POSTv res.
        CUSTOM_FFI Delete_callback inputs
          (events ++ [IO_event (ExtCall «hints»)
            (MAP (n2w o ORD) (explode s))
            (ZIP (xss,write_bytes xss hs))]) tb *
        W8ARRAY arrvv (write_bytes xss hs)`
  >- (
    xffi>>xsimpl>>
    simp[CUSTOM_FFI_def]>>
    (* conf *)
    qexists_tac`MAP (n2w o ORD) (explode s)`>>
    (* frame *)
    qexists_tac`emp`>>
    xsimpl>>
    (* state *)
    qmatch_goalsub_abbrev_tac`FFI_part ss`>>
    qexists_tac`ss`>>
    qexists_tac`update`>>
    qexists_tac`names`>>
    qexists_tac`events`>>
    rw[]
    >- EVAL_TAC
    >- gvs[STRING_TYPE_def,MAP_MAP_o,CHR_w2n_n2w_ORD_I]
    >- EVAL_TAC
    >- xsimpl>>
    simp[update_def,Abbr`ss`,update_hints_def]>>
    xsimpl>>rw[])>>
  xlet_auto
  >-(
    xsimpl>>fs[LENGTH_write_bytes]>>
    metis_tac[])>>
  xcon>>xsimpl>>
  qexists_tac`xss`>>xsimpl>>
  metis_tac[]
QED

Theorem parse_step_Delete:
  LENGTH step_arr = 17 ⇒
  app (p:'ffi ffi_proj) parse_step_v [step_arrv; buf_arrv]
    (CUSTOM_FFI Step (Delete xs ys :: inputs) events tb *
     W8ARRAY buf_arrv buf_arr *
     W8ARRAY step_arrv step_arr)
    (POSTv res.
       SEP_EXISTS step_arr1 buf_arrv buf_arr delete_events hs.
         CUSTOM_FFI Delete_callback inputs (events ++ delete_events) tb *
         W8ARRAY buf_arrv buf_arr *
         W8ARRAY step_arrv step_arr1 *
         cond (LENGTH step_arr1 = 17 ∧ CHR (w2n (HD step_arr1)) = #"d" ∧
               is_delete_events delete_events ∧
               ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME (Del hs)) v ∧
                   res = Conv NONE [buf_arrv; v]))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "-" "parse_step_v_def") >>
  qabbrev_tac ‘a1 = write_bytes step_arr (100w::xs)’ >>
  qabbrev_tac ‘event1 = IO_event (ExtCall «step») [] (ZIP (step_arr,a1))’ >>
  xlet ‘POSTv res.
      CUSTOM_FFI (Delete_hints ys) inputs (events ++ [event1]) tb *
      W8ARRAY buf_arrv buf_arr *
      W8ARRAY step_arrv a1’
  >-
   (xffi >>
    gvs [CUSTOM_FFI_def,implode_def] >>
    xsimpl >>
    qexists_tac ‘W8ARRAY buf_arrv buf_arr’ >> xsimpl >>
    irule_at Any SEP_IMP_REFL >>
    conj_tac >- EVAL_TAC >>
    conj_tac >- EVAL_TAC >>
    simp [update_def,update_step_def] >>
    gvs [names_def,SEP_CLAUSES] >>
    xsimpl) >>
  Cases_on ‘step_arr’ >> gvs [write_bytes_def,Abbr‘a1’] >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  gvs [CHAR_def,WORD_def] >>
  xmatch >>
  xlet_auto >- (xsimpl >> gvs [LENGTH_write_bytes]) >>
  gvs [] >>
  xlet ‘POSTv res.
    SEP_EXISTS buf_arrv1 buf_arr1 hs wss3 io3.
      W8ARRAY step_arrv (100w::write_bytes t xs) *
      W8ARRAY buf_arrv1 buf_arr1 *
      CUSTOM_FFI Delete_callback inputs (events ++ [event1;
        IO_event (ExtCall «hints») wss3 io3]) tb *
      cond (∃v. res = Conv NONE [buf_arrv1; v] ∧
                LIST_TYPE NUM hs v)’
  >- (
    xapp>>
    xsimpl>>
    first_x_assum $ irule_at Any>>
    qexists_tac`tb`>>
    qexists_tac`inputs`>>
    qexists_tac`ys`>>
    qexists_tac`events ++ [event1]`>>
    qexists_tac`W8ARRAY step_arrv (100w::write_bytes t xs)`>>
    xsimpl>>
    rw[]
    >- (
      DEP_REWRITE_TAC[LENGTH_TAKE,LENGTH_DROP,LENGTH_write_bytes]>>
      gvs[])>>
    first_x_assum (irule_at Any)>>
    rename1`IO_event _ sss3 io3`>>
    qexists_tac`io3`>>
    qexists_tac`sss3`>>
    PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
    REWRITE_TAC[APPEND]>>xsimpl)>>
  qmatch_goalsub_abbrev_tac`[event1; event2]`>>
  gvs [] >>
  xmatch >>
  xlet_auto >- (xcon >> xsimpl) >>
  xlet_auto >- (xcon >> xsimpl) >>
  xcon >> xsimpl >>
  simp [PULL_EXISTS] >> xsimpl >>
  qexists ‘[event1; event2]’ >> xsimpl >>
  gvs [] >>
  gvs [OPTION_TYPE_def, DISTRUP_DISTRUP_TYPE_def] >>
  first_x_assum $ irule_at Any >>
  simp [GSYM PULL_EXISTS] >>
  conj_tac
  >-
   (‘LENGTH (write_bytes t xs) = 16’ by (rewrite_tac [LENGTH_write_bytes] >> gvs []) >>
    gvs [LENGTH_EQ_NUM_compute]) >>
  unabbrev_all_tac>>
  gvs [is_delete_events_def,LENGTH_write_bytes,MAP_ZIP]
QED

Theorem do_callback_Delete:
  STRING_TYPE res resv ∧
  LENGTH step_arr = 17 ∧ CHR (w2n (HD step_arr)) = #"d" ⇒
  app (p:'ffi ffi_proj) do_callback_v [resv; step_arrv]
    (CUSTOM_FFI Delete_callback inputs events tb *
     W8ARRAY step_arrv step_arr)
    (POSTv uv.
         CUSTOM_FFI Step inputs (events ++
            [IO_event (ExtCall «callback») (MAP (n2w ∘ ORD) (explode res))
                 (ZIP (step_arr,step_arr))]) tb *
         W8ARRAY step_arrv step_arr)
Proof
  rw[]>>irule do_callback_gen>>fs[match_callback_def]
QED

(* Validate_UNSAT events
  TODO: can say more about ss2/ss3 *)
Definition is_validate_events_def:
  is_validate_events validate_events ⇔
    ∃xs1.
      validate_events = [IO_event (ExtCall «step»)   [] xs1] ∧
      LENGTH xs1 = 17 ∧
      SND (HD xs1) = n2w (ORD #"V")
End

Theorem parse_step_Validate_UNSAT:
  LENGTH step_arr = 17 ⇒
  app (p:'ffi ffi_proj) parse_step_v [step_arrv; buf_arrv]
    (CUSTOM_FFI Step (Validate_UNSAT xs :: inputs) events tb *
     W8ARRAY buf_arrv buf_arr *
     W8ARRAY step_arrv step_arr)
    (POSTv res.
       SEP_EXISTS step_arr1 buf_arrv buf_arr delete_events hs.
         CUSTOM_FFI Validate_UNSAT_callback inputs (events ++ delete_events) tb *
         W8ARRAY buf_arrv buf_arr *
         W8ARRAY step_arrv step_arr1 *
         cond (LENGTH step_arr1 = 17 ∧ CHR (w2n (HD step_arr1)) = #"V" ∧
               is_validate_events delete_events ∧
               ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME ValidateUnsat) v ∧
                   res = Conv NONE [buf_arrv; v]))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "-" "parse_step_v_def") >>
  qabbrev_tac ‘a1 = write_bytes step_arr (86w::xs)’ >>
  qabbrev_tac ‘event1 = IO_event (ExtCall «step») [] (ZIP (step_arr,a1))’ >>
  xlet ‘POSTv res.
      CUSTOM_FFI Validate_UNSAT_callback inputs (events ++ [event1]) tb *
      W8ARRAY buf_arrv buf_arr *
      W8ARRAY step_arrv a1’
  >-
   (xffi >>
    gvs [CUSTOM_FFI_def,implode_def] >>
    xsimpl >>
    qexists_tac ‘W8ARRAY buf_arrv buf_arr’ >> xsimpl >>
    irule_at Any SEP_IMP_REFL >>
    conj_tac >- EVAL_TAC >>
    conj_tac >- EVAL_TAC >>
    simp [update_def,update_step_def] >>
    gvs [names_def,SEP_CLAUSES] >>
    xsimpl) >>
  Cases_on ‘step_arr’ >> gvs [write_bytes_def,Abbr‘a1’] >>
  xlet_auto >- xsimpl >>
  xlet_auto >- xsimpl >>
  gvs [CHAR_def,WORD_def] >>
  xmatch >>
  xlet_autop>>
  xlet_autop>>
  xcon >> xsimpl >>
  simp [PULL_EXISTS] >> xsimpl >>
  qexists ‘[event1]’ >> xsimpl >>
  gvs [] >>
  gvs [OPTION_TYPE_def, DISTRUP_DISTRUP_TYPE_def] >>
  simp [GSYM PULL_EXISTS] >>
  conj_tac
  >-
   (‘LENGTH (write_bytes t xs) = 16’ by (rewrite_tac [LENGTH_write_bytes] >> gvs []) >>
    gvs [LENGTH_EQ_NUM_compute]) >>
  unabbrev_all_tac>>
  gvs [is_validate_events_def,LENGTH_write_bytes,MAP_ZIP]
QED

Theorem do_callback_Validate_UNSAT:
  STRING_TYPE res resv ∧
  LENGTH step_arr = 17 ∧ CHR (w2n (HD step_arr)) = #"V" ⇒
  app (p:'ffi ffi_proj) do_callback_v [resv; step_arrv]
    (CUSTOM_FFI Validate_UNSAT_callback inputs events  tb*
     W8ARRAY step_arrv step_arr)
    (POSTv uv.
         CUSTOM_FFI Step inputs (events ++
            [IO_event (ExtCall «callback») (MAP (n2w ∘ ORD) (explode res))
                 (ZIP (step_arr,step_arr))]) tb *
         W8ARRAY step_arrv step_arr)
Proof
  rw[]>>irule do_callback_gen>>fs[match_callback_def]
QED

Definition is_output_event_def:
  is_output_event c success event ⇔
    ∃xs ss.
      event = IO_event (ExtCall «callback») ss xs ∧
      LENGTH xs = 17 ∧
      CHR (w2n (HD (MAP SND xs))) = c ∧
      ss ≠ [] ∧
      CHR (w2n (HD ss)) = success
End

Inductive events_ok:
[~init:]
  events_ok st [] [] st
[~produce:]
  events_ok st events aevents (SOME (fmlls, Clist, b)) ∧
  is_produce_events n vc produce_events ∧
  is_output_event #"a" #"1" output_event ∧
  check_distrup_list (Lrup n vc hints) fmlls Clist b = SOME (fmlls', Clist', b')
  ⇒
  events_ok st (events ++ produce_events ++ [output_event]) (aevents ++ [Lrup n vc hints]) (SOME (fmlls', Clist', b'))
[~produce_Fail:]
  events_ok st events aevents (SOME (fmlls, Clist, b)) ∧
  is_produce_events n vc produce_events ∧
  is_output_event #"a" #"0" output_event ∧
  check_distrup_list (Lrup n vc hints) fmlls Clist b = NONE
  ⇒
  events_ok st (events ++ produce_events ++ [output_event]) (aevents ++ [Lrup n vc hints]) NONE
[~produce_None:]
  events_ok st events aevents NONE ∧
  is_produce_events n vc produce_events ∧
  is_output_event #"a" #"0" output_event
  ⇒
  events_ok st (events ++ produce_events ++ [output_event]) (aevents ++ [Lrup n vc hints]) NONE
[~import:]
  events_ok st events aevents (SOME (fmlls, Clist, b)) ∧
  is_import_events n vc import_events ∧
  is_output_event #"i" #"1" output_event ∧
  check_distrup_list (Import n vc) fmlls Clist b = SOME (fmlls', Clist', b')
  ⇒
  events_ok st (events ++ import_events ++ [output_event]) (aevents ++ [Import n vc]) (SOME (fmlls', Clist', b'))
[~import_None:]
  events_ok st events aevents NONE ∧
  is_import_events n vc import_events ∧
  is_output_event #"i" #"0" output_event
  ⇒
  events_ok st (events ++ import_events ++ [output_event]) (aevents ++ [Import n vc]) NONE
[~delete:]
  events_ok st events aevents (SOME (fmlls, Clist, b)) ∧
  is_delete_events delete_events ∧
  is_output_event #"d" #"1" output_event ∧
  check_distrup_list (Del hints) fmlls Clist b = SOME (fmlls', Clist', b')
  ⇒
  events_ok st (events ++ delete_events ++ [output_event]) (aevents ++ [Del hints]) (SOME (fmlls', Clist', b'))
[~delete_None:]
  events_ok st events aevents NONE ∧
  is_delete_events delete_events ∧
  is_output_event #"d" #"0" output_event
  ⇒
  events_ok st (events ++ delete_events ++ [output_event]) (aevents ++ [Del hints]) NONE
[~validate:]
  events_ok st events aevents (SOME (fmlls, Clist, b)) ∧
  is_validate_events validate_events ∧
  is_output_event #"V" #"1" output_event ∧
  check_distrup_list Validate_Unsat fmlls Clist b = SOME (fmlls', Clist', b')
  ⇒
  events_ok st (events ++ validate_events ++ [output_event]) (aevents ++ [Validate_Unsat]) (SOME (fmlls', Clist', b'))
[~validate_Fail:]
  events_ok st events aevents (SOME (fmlls, Clist, b)) ∧
  is_validate_events validate_events ∧
  is_output_event #"V" #"0" output_event ∧
  check_distrup_list Validate_Unsat fmlls Clist b = NONE
  ⇒
  events_ok st (events ++ validate_events ++ [output_event]) (aevents ++ [Validate_Unsat]) NONE
[~validate_None:]
  events_ok st events aevents NONE ∧
  is_validate_events validate_events ∧
  is_output_event #"V" #"0" output_event
  ⇒
  events_ok st (events ++ validate_events ++ [output_event]) (aevents ++ [Validate_Unsat]) NONE
End

Theorem check_top_NONE:
  NUM lno lnov ∧
  DISTRUP_DISTRUP_TYPE inst instv ∧
  stv = Conv (SOME (TypeStamp «None» 2)) [] ⇒
  app (p:'ffi ffi_proj) check_top_v [lnov; instv; stv]
      (emp)
      (POSTv res.
        &(res =
          Conv NONE [Conv (SOME (TypeStamp «None» 2)) [];
            Litv (StrLit «»)]))
Proof
  rw[]>>
  xcf_with_def (fetch "-" "check_top_v_def") >>
  xmatch>>
  xlet_autop>>
  xcon>>xsimpl
QED

Theorem check_top_SOME:
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls fmllsv ∧
  WORD8 b bv ∧
  DISTRUP_DISTRUP_TYPE inst instv ∧
  bnd_fml fmlls (LENGTH Clist) ∧
  stv =
    Conv (SOME (TypeStamp «Some» 2))
      [Conv NONE [fmlv; Carrv; bv]] ⇒
  app (p:'ffi ffi_proj) check_top_v [lnov; instv; stv]
      (ARRAY fmlv fmllsv *
       W8ARRAY Carrv Clist)
      (POSTv res.
         SEP_EXISTS v1 v2 msg stopt.
         &(res = Conv NONE [v1;v2] ∧
           STRING_TYPE msg v2) *
         case check_distrup_list inst fmlls Clist b of
           NONE =>
            &(v1 = Conv (SOME (TypeStamp «None» 2)) [])
         | SOME (fmlls', Clist', b') =>
            SEP_EXISTS v11 v12 v13 fmllsv'.
            ARRAY v11 fmllsv' *
            W8ARRAY v12 Clist' *
            &(
              v1 = Conv (SOME (TypeStamp «Some» 2))
                [Conv NONE [v11;v12;v13]] ∧
              WORD8 b' v13 ∧
              LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls' fmllsv'
            )
      )
Proof
  rw[]>>
  xcf_with_def (fetch "-" "check_top_v_def") >>
  xmatch>>
  Cases_on`check_distrup_list inst fmlls Clist b`
  >- (
    simp[]>>
    xhandle`POSTe e.
      &(Fail_exn e ∧ check_distrup_list inst fmlls Clist b = NONE)`
    >- (
      xlet_autop>>
      xsimpl)>>
    gvs[ccnf_arrayProgTheory.Fail_exn_def]>>
    xcases>>
    xlet_autop>>
    xcon>>xsimpl>>
    metis_tac[])>>
  `?fmlls' Clist' b'. x = (fmlls', Clist', b')` by metis_tac[PAIR]>>
  simp[]>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_autop >- xsimpl>>
  gvs[]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>
  xsimpl
QED

Theorem SEP_IMP_REFL_emp:
  p ==>> p * emp
Proof
  xsimpl
QED

(* Allow any state or SOME? *)
Definition full_events_ok_def:
  full_events_ok st events ⇔
    ∃xs final aevents st'.
      events = xs ++ [final] ∧
      events_ok st xs aevents st' ∧
      is_final_event final
End

Theorem loop_NONE:
  ∀inputs lno lnov events aevents step_arr step_arrv buf_arr buf_arrv stv.
    NUM lno lnov ∧
    stv = Conv (SOME (TypeStamp «None» 2)) [] ∧
    events_ok st events aevents NONE ∧
    LENGTH step_arr = 17 ⇒
    app (p:'ffi ffi_proj) loop_v [step_arrv; buf_arrv; stv; lnov]
        (CUSTOM_FFI Step inputs events tb *
         W8ARRAY buf_arrv buf_arr *
         W8ARRAY step_arrv step_arr)
        (POSTv res.
           SEP_EXISTS step_arr1 buf_arrv buf_arr new_events.
             CUSTOM_FFI Terminate [] new_events tb *
             W8ARRAY buf_arrv buf_arr *
             W8ARRAY step_arrv step_arr1 *
             cond (full_events_ok st new_events))
Proof
  Induct
  >-
   (rpt strip_tac >>
    xcf_with_def (fetch "-" "loop_v_def") >>
    xlet_auto_spec (SOME parse_step_NIL)
    >-
     (xsimpl >>
      qrefinel [‘_’,‘tb’] >>
      xsimpl >>
      rw [PULL_EXISTS] >>
      first_x_assum $ irule_at Any >> xsimpl) >>
    gvs [] >> xmatch >>
    gvs [OPTION_TYPE_def] >>
    xmatch >> xcon >>
    xsimpl >>
    qexistsl [‘buf_arrv’,‘buf_arr’,‘(events ++ [final_event])’] >>
    xsimpl >>
    simp [full_events_ok_def] >>
    first_x_assum $ irule_at Any) >>
  Cases_on ‘h’
  >~ [‘Produce xs ys zs’] >-
   (rpt strip_tac >>
    xcf_with_def (fetch "-" "loop_v_def") >>
    xlet ‘POSTv res.
            SEP_EXISTS step_arr1 buf_arrv buf_arr produce_events cl hs i.
              CUSTOM_FFI Produce_callback inputs (events ++ produce_events) tb *
              W8ARRAY buf_arrv buf_arr * W8ARRAY step_arrv step_arr1 *
              cond (LENGTH step_arr1 = 17 ∧ CHR (w2n (HD step_arr1)) = #"a" ∧
                    is_produce_events i cl produce_events ∧
                    ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME (Lrup i cl hs)) v ∧
                        res = Conv NONE [buf_arrv; v])’
    >-
     (xapp_spec parse_step_Produce >>
      rw[])>>
    gvs [] >>
    xmatch >> gvs [OPTION_TYPE_def] >>
    xmatch >> gvs [] >>
    xlet_autop>>
    xmatch>>
    xmatch>>
    xlet_autop>>
    drule_all do_callback_Produce>>
    disch_then (qspecl_then[`tb`,`step_arrv`,`p`,`inputs`] assume_tac)>>
    xlet_autop>>
    xlet_autop>>
    xapp>>xsimpl>>
    first_x_assum $ irule_at Any>>
    irule_at Any SEP_IMP_REFL_emp>>
    irule_at Any events_ok_produce_None>>
    fs[is_output_event_def]>>
    metis_tac[])
  >~ [‘Import xs ys’] >-
    (rpt strip_tac >>
    xcf_with_def (fetch "-" "loop_v_def") >>
    xlet ‘POSTv res.
            SEP_EXISTS step_arr1 buf_arrv buf_arr import_events cl i.
              CUSTOM_FFI Import_callback inputs (events ++ import_events) tb *
              W8ARRAY buf_arrv buf_arr * W8ARRAY step_arrv step_arr1 *
              cond (LENGTH step_arr1 = 17 ∧ CHR (w2n (HD step_arr1)) = #"i" ∧
                    is_import_events i cl import_events ∧
                    ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME (Import i cl)) v ∧
                        res = Conv NONE [buf_arrv; v])’
    >-
     (xapp_spec parse_step_Import >>
     rw[])>>
    gvs [] >>
    xmatch >> gvs [OPTION_TYPE_def] >>
    xmatch >> gvs [] >>
    xlet_autop>>
    xmatch>>
    xmatch>>
    xlet_autop>>
    drule_all do_callback_Import>>
    disch_then (qspecl_then[`tb`,`step_arrv`,`p`,`inputs`] assume_tac)>>
    xlet_autop>>
    xlet_autop>>
    xapp>>xsimpl>>
    first_x_assum $ irule_at Any>>
    irule_at Any SEP_IMP_REFL_emp>>
    irule_at Any events_ok_import_None>>
    fs[is_output_event_def]>>
    metis_tac[])
  >~ [‘Delete xs ys’] >-
    (rpt strip_tac >>
    xcf_with_def (fetch "-" "loop_v_def") >>
    xlet ‘POSTv res.
            SEP_EXISTS step_arr1 buf_arrv buf_arr delete_events hints.
              CUSTOM_FFI Delete_callback inputs (events ++ delete_events) tb *
              W8ARRAY buf_arrv buf_arr * W8ARRAY step_arrv step_arr1 *
              cond (LENGTH step_arr1 = 17 ∧ CHR (w2n (HD step_arr1)) = #"d" ∧
                    is_delete_events delete_events ∧
                    ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME (Del hints)) v ∧
                        res = Conv NONE [buf_arrv; v])’
    >-
     (xapp_spec parse_step_Delete >>
     rw[])>>
    gvs [] >>
    xmatch >> gvs [OPTION_TYPE_def] >>
    xmatch >> gvs [] >>
    xlet_autop>>
    xmatch>>
    xmatch>>
    xlet_autop>>
    drule_all do_callback_Delete>>
    disch_then (qspecl_then[`tb`,`step_arrv`,`p`,`inputs`] assume_tac)>>
    xlet_autop>>
    xlet_autop>>
    xapp>>xsimpl>>
    first_x_assum $ irule_at Any>>
    irule_at Any SEP_IMP_REFL_emp>>
    irule_at Any events_ok_delete_None>>
    fs[is_output_event_def]>>
    metis_tac[])
  >~ [‘Validate_UNSAT’] >-
    (rpt strip_tac >>
    xcf_with_def (fetch "-" "loop_v_def") >>
    xlet ‘POSTv res.
            SEP_EXISTS step_arr1 buf_arrv buf_arr validate_events.
              CUSTOM_FFI Validate_UNSAT_callback inputs (events ++ validate_events) tb *
              W8ARRAY buf_arrv buf_arr * W8ARRAY step_arrv step_arr1 *
              cond (LENGTH step_arr1 = 17 ∧ CHR (w2n (HD step_arr1)) = #"V" ∧
                    is_validate_events validate_events ∧
                    ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME ValidateUnsat) v ∧
                        res = Conv NONE [buf_arrv; v])’
    >-
     (xapp_spec parse_step_Validate_UNSAT >>
      xsimpl>>
      irule_at Any SEP_IMP_REFL_emp>>
      rw[]>>xsimpl>>
      first_x_assum (irule_at Any)>>
      xsimpl)>>
    gvs [] >>
    xmatch >> gvs [OPTION_TYPE_def] >>
    xmatch >> gvs [] >>
    xlet_autop>>
    xmatch>>
    xmatch>>
    xlet_autop>>
    drule_all do_callback_Validate_UNSAT>>
    disch_then (qspecl_then[`tb`,`step_arrv`,`p`,`inputs`] assume_tac)>>
    xlet_autop>>
    xlet_autop>>
    xapp>>xsimpl>>
    first_x_assum $ irule_at Any>>
    irule_at Any SEP_IMP_REFL_emp>>
    irule_at Any events_ok_validate_None>>
    fs[is_output_event_def]>>
    metis_tac[])
QED

Theorem loop_SOME:
  ∀inputs lno lnov events aevents fmlls fmllsv Clist step_arr step_arrv
    buf_arr buf_arrv b bv stv fmlv Carrv.
    NUM lno lnov ∧
    LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls fmllsv ∧
    WORD8 b bv ∧
    bnd_fml fmlls (LENGTH Clist) ∧
    events_ok st events aevents (SOME (fmlls, Clist, b)) ∧
    stv =
      Conv (SOME (TypeStamp «Some» 2))
        [Conv NONE [fmlv; Carrv; bv]] ⇒
    LENGTH step_arr = 17 ⇒
    app (p:'ffi ffi_proj) loop_v [step_arrv; buf_arrv; stv; lnov]
        (CUSTOM_FFI Step inputs events tb *
         ARRAY fmlv fmllsv *
         W8ARRAY Carrv Clist *
         W8ARRAY buf_arrv buf_arr *
         W8ARRAY step_arrv step_arr)
        (POSTv res.
           SEP_EXISTS step_arr1 buf_arrv buf_arr new_events.
             CUSTOM_FFI Terminate [] new_events tb *
             W8ARRAY buf_arrv buf_arr *
             W8ARRAY step_arrv step_arr1 *
             cond (full_events_ok st new_events))
Proof
  Induct
  >-
   (rpt strip_tac >>
    xcf_with_def (fetch "-" "loop_v_def") >>
    xlet_auto_spec (SOME parse_step_NIL)
    >-
     (xsimpl >>
      qrefinel [‘_’,‘tb’] >>
      xsimpl >>
      rw [PULL_EXISTS] >>
      first_x_assum $ irule_at Any >> xsimpl) >>
    gvs [] >> xmatch >>
    gvs [OPTION_TYPE_def] >>
    xmatch >> xcon >>
    xsimpl >>
    qexistsl [‘buf_arrv’,‘buf_arr’,‘(events ++ [final_event])’] >>
    xsimpl >>
    simp [full_events_ok_def] >>
    first_x_assum $ irule_at Any) >>
  Cases_on ‘h’
  >~ [‘Produce xs ys zs’] >-
   (rpt strip_tac >>
    xcf_with_def (fetch "-" "loop_v_def") >>
    xlet ‘POSTv res.
            SEP_EXISTS step_arr1 buf_arrv buf_arr produce_events cl hs i.
              CUSTOM_FFI Produce_callback inputs (events ++ produce_events) tb *
              W8ARRAY buf_arrv buf_arr * W8ARRAY step_arrv step_arr1 *
              ARRAY fmlv fmllsv *
              W8ARRAY Carrv Clist *
              cond (LENGTH step_arr1 = 17 ∧ CHR (w2n (HD step_arr1)) = #"a" ∧
                    is_produce_events i cl produce_events ∧
                    ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME (Lrup i cl hs)) v ∧
                        res = Conv NONE [buf_arrv; v])’
    >-
     (xapp_spec parse_step_Produce >>
      qrefinel [‘_’,‘zs’,‘ys’,‘xs’,‘tb’,‘step_arr’,‘inputs’,‘events’,‘buf_arr’] >>
      xsimpl >>
      rw [] >>
      first_x_assum $ irule_at Any >>
      first_x_assum $ irule_at Any >>
      xsimpl) >>
    drule_at Any do_callback_Produce>>
    disch_then $ drule_at Any>>
    strip_tac>>
    gvs [] >>
    xmatch >> gvs [OPTION_TYPE_def] >>
    xmatch >> gvs [] >>
    xlet_auto_spec (SOME check_top_SOME)
    >-
      (xsimpl>>metis_tac[])>>
    TOP_CASE_TAC
    >- ( (* None *)
      xpull>>
      xmatch>>
      xmatch>>
      xlet_autop>>
      first_x_assum drule>>
      disch_then (qspecl_then[`tb`,`step_arrv`,`p`,`inputs`] assume_tac)>>
      xlet_autop>>
      xlet_autop>>
      xapp_spec loop_NONE>>xsimpl>>
      irule_at Any SEP_IMP_REFL_emp>>
      pop_assum $ irule_at Any>>
      irule_at Any events_ok_produce_Fail>>
      fs[is_output_event_def]>>
      rpt $ first_assum $ irule_at Any>>
      rw [] >>
      pop_assum $ irule_at Any>>
      xsimpl >>
      rename [‘W8ARRAY x1 x2’] >>
      qexistsl [‘x2’,‘x1’] >> xsimpl)>>
    `∃fmlls' Clist' b'.
      x = (fmlls',Clist',b')` by metis_tac[PAIR]>>
    fs[]>>
    xpull>>
    xmatch>>
    xmatch>>
    xlet_autop>>
    first_x_assum drule>>
    disch_then (qspecl_then[`tb`,`step_arrv`,`p`,`inputs`] assume_tac)>>
    xlet_autop>>
    xlet_autop>>
    xapp>>xsimpl>>
    irule_at Any SEP_IMP_REFL_emp>>
    pop_assum $ irule_at Any>>
    first_x_assum $ irule_at Any>>
    first_x_assum $ irule_at Any>>
    simp[GSYM PULL_EXISTS]>>
    CONJ_TAC >-
      metis_tac[distrup_listTheory.check_distrup_list_bnd_fml]>>
    irule_at Any events_ok_produce>>
    fs[is_output_event_def]>>
    metis_tac[])
  >~ [‘Import xs ys’] >-
    (rpt strip_tac >>
    xcf_with_def (fetch "-" "loop_v_def") >>
    xlet ‘POSTv res.
            SEP_EXISTS step_arr1 buf_arrv buf_arr import_events cl i.
              CUSTOM_FFI Import_callback inputs (events ++ import_events) tb *
              W8ARRAY buf_arrv buf_arr * W8ARRAY step_arrv step_arr1 *
              ARRAY fmlv fmllsv *
              W8ARRAY Carrv Clist *
              cond (LENGTH step_arr1 = 17 ∧ CHR (w2n (HD step_arr1)) = #"i" ∧
                    is_import_events i cl import_events ∧
                    ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME (Import i cl)) v ∧
                        res = Conv NONE [buf_arrv; v])’
    >-
     (xapp_spec parse_step_Import >>
      qrefinel [‘_’,‘ys’,‘xs’,‘tb’,‘step_arr’,‘inputs’,‘events’,‘buf_arr’] >>
      xsimpl >>
      rw [] >>
      first_x_assum $ irule_at Any >>
      first_x_assum $ irule_at Any >>
      xsimpl) >>
    drule_at Any do_callback_Import>>
    disch_then $ drule_at Any>>
    strip_tac>>
    gvs [] >>
    xmatch >> gvs [OPTION_TYPE_def] >>
    xmatch >> gvs [] >>
    xlet_auto_spec (SOME check_top_SOME)
    >-
      (xsimpl>>metis_tac[])>>
    TOP_CASE_TAC
    >- ( (* None *)
      gvs[check_distrup_list_def])>>
    `∃fmlls' Clist' b'.
      x = (fmlls',Clist',b')` by metis_tac[PAIR]>>
    fs[]>>
    xpull>>
    xmatch>>
    xmatch>>
    xlet_autop>>
    first_x_assum drule>>
    disch_then (qspecl_then[`tb`,`step_arrv`,`p`,`inputs`] assume_tac)>>
    xlet_autop>>
    xlet_autop>>
    xapp>>xsimpl>>
    irule_at Any SEP_IMP_REFL_emp>>
    pop_assum $ irule_at Any>>
    first_x_assum $ irule_at Any>>
    first_x_assum $ irule_at Any>>
    simp[GSYM PULL_EXISTS]>>
    CONJ_TAC >-
      metis_tac[distrup_listTheory.check_distrup_list_bnd_fml]>>
    irule_at Any events_ok_import>>
    fs[is_output_event_def]>>
    metis_tac[])
  >~ [‘Delete xs ys’] >-
    (rpt strip_tac >>
    xcf_with_def (fetch "-" "loop_v_def") >>
    xlet ‘POSTv res.
            SEP_EXISTS step_arr1 buf_arrv buf_arr delete_events hs.
              CUSTOM_FFI Delete_callback inputs (events ++ delete_events) tb *
              W8ARRAY buf_arrv buf_arr * W8ARRAY step_arrv step_arr1 *
              ARRAY fmlv fmllsv *
              W8ARRAY Carrv Clist *
              cond (LENGTH step_arr1 = 17 ∧ CHR (w2n (HD step_arr1)) = #"d" ∧
                    is_delete_events delete_events ∧
                    ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME (Del hs)) v ∧
                        res = Conv NONE [buf_arrv; v])’
    >-
     (xapp_spec parse_step_Delete >>
      qrefinel [‘_’,‘ys’,‘xs’,‘tb’,‘step_arr’,‘inputs’,‘events’,‘buf_arr’] >>
      xsimpl >>
      rw [] >>
      first_x_assum $ irule_at Any >>
      first_x_assum $ irule_at Any >>
      xsimpl) >>
    drule_at Any do_callback_Delete>>
    disch_then $ drule_at Any>>
    strip_tac>>
    gvs [] >>
    xmatch >> gvs [OPTION_TYPE_def] >>
    xmatch >> gvs [] >>
    xlet_auto_spec (SOME check_top_SOME)
    >-
      (xsimpl>>metis_tac[])>>
    TOP_CASE_TAC
    >- ( (* None *)
      gvs[check_distrup_list_def])>>
    `∃fmlls' Clist' b'.
      x = (fmlls',Clist',b')` by metis_tac[PAIR]>>
    fs[]>>
    xpull>>
    xmatch>>
    xmatch>>
    xlet_autop>>
    first_x_assum drule>>
    disch_then (qspecl_then[`tb`,`step_arrv`,`p`,`inputs`] assume_tac)>>
    xlet_autop>>
    xlet_autop>>
    xapp>>xsimpl>>
    irule_at Any SEP_IMP_REFL_emp>>
    pop_assum $ irule_at Any>>
    first_x_assum $ irule_at Any>>
    first_x_assum $ irule_at Any>>
    simp[GSYM PULL_EXISTS]>>
    CONJ_TAC >-
      metis_tac[distrup_listTheory.check_distrup_list_bnd_fml]>>
    irule_at Any events_ok_delete>>
    fs[is_output_event_def]>>
    metis_tac[])
  >~ [‘Validate_UNSAT’] >-
    (rpt strip_tac >>
    xcf_with_def (fetch "-" "loop_v_def") >>
    xlet ‘POSTv res.
            SEP_EXISTS step_arr1 buf_arrv buf_arr validate_events.
              CUSTOM_FFI Validate_UNSAT_callback inputs (events ++ validate_events) tb *
              W8ARRAY buf_arrv buf_arr * W8ARRAY step_arrv step_arr1 *
              ARRAY fmlv fmllsv *
              W8ARRAY Carrv Clist *
              cond (LENGTH step_arr1 = 17 ∧ CHR (w2n (HD step_arr1)) = #"V" ∧
                    is_validate_events validate_events ∧
                    ∃v. OPTION_TYPE DISTRUP_DISTRUP_TYPE (SOME ValidateUnsat) v ∧
                        res = Conv NONE [buf_arrv; v])’
    >-
     (xapp_spec parse_step_Validate_UNSAT >>
      qrefinel [‘_’,‘xs’,‘tb’,‘step_arr’,‘inputs’,‘events’,‘buf_arr’] >>
      xsimpl >>
      simp[Once (GSYM STAR_ASSOC)]>>
      irule_at Any SEP_IMP_REFL>>
      rw[]>>
      first_x_assum (irule_at Any)>>
      xsimpl)>>
    drule_at Any do_callback_Validate_UNSAT>>
    disch_then $ drule_at Any>>
    strip_tac>>
    gvs [] >>
    xmatch >> gvs [OPTION_TYPE_def] >>
    xmatch >> gvs [] >>
    xlet_auto_spec (SOME check_top_SOME)
    >-
      (xsimpl>>metis_tac[])>>
    TOP_CASE_TAC
    >- ( (* None *)
      xpull>>
      xmatch>>
      xmatch>>
      xlet_autop>>
      first_x_assum drule>>
      disch_then (qspecl_then[`tb`,`step_arrv`,`p`,`inputs`] assume_tac)>>
      xlet_autop>>
      xlet_autop>>
      xapp_spec loop_NONE>>xsimpl>>
      irule_at Any SEP_IMP_REFL_emp>>
      pop_assum $ irule_at Any>>
      irule_at Any events_ok_validate_Fail>>
      fs[is_output_event_def]>>
      fs[is_output_event_def]>>
      rpt $ first_assum $ irule_at Any>>
      rw [] >>
      pop_assum $ irule_at Any>>
      xsimpl >>
      rename [‘W8ARRAY x1 x2’] >>
      qexistsl [‘x2’,‘x1’] >> xsimpl)>>
    `∃fmlls' Clist' b'.
      x = (fmlls',Clist',b')` by metis_tac[PAIR]>>
    fs[]>>
    xpull>>
    xmatch>>
    xmatch>>
    xlet_autop>>
    first_x_assum drule>>
    disch_then (qspecl_then[`tb`,`step_arrv`,`p`,`inputs`] assume_tac)>>
    xlet_autop>>
    xlet_autop>>
    xapp>>xsimpl>>
    irule_at Any SEP_IMP_REFL_emp>>
    pop_assum $ irule_at Any>>
    first_x_assum $ irule_at Any>>
    first_x_assum $ irule_at Any>>
    simp[GSYM PULL_EXISTS]>>
    CONJ_TAC >-
      metis_tac[distrup_listTheory.check_distrup_list_bnd_fml]>>
    irule_at Any events_ok_validate>>
    fs[is_output_event_def]>>
    metis_tac[])
QED

Definition init_st_def:
  init_st = (SOME (REPLICATE 4096n (NONE:vcclause option), REPLICATE 1024n (0w:word8), (1w:word8)))
End

Theorem main_spec:
  app (p:'ffi ffi_proj) main_v [Conv NONE []]
    (CUSTOM_FFI Step inputs [] tb)
    (POSTv res.
       SEP_EXISTS events.
         CUSTOM_FFI Terminate [] events tb *
         cond (full_events_ok init_st events))
Proof
  rpt strip_tac >>
  xcf_with_def (fetch "-" "main_v_def") >>
  xmatch  >> gvs [] >>
  rpt xlet_autop>>
  xapp_spec loop_SOME >>
  qexists ‘emp’ >> xsimpl >>
  qexists_tac`tb`>>
  first_x_assum $ irule_at Any>>
  irule_at Any events_ok_init>>
  qexists_tac`inputs`>>
  qexists ‘REPLICATE 4096 NONE’ >>
  xsimpl >>
  conj_tac >-
   (gvs [ccnf_listTheory.bnd_fml_def,miscTheory.any_el_ALT,EL_REPLICATE, SF CONJ_ss]) >>
  conj_tac >-
   (gvs [LIST_REL_EL_EQN,OPTION_TYPE_def,EL_REPLICATE]) >>
  rw [] >> rename [‘CUSTOM_FFI Terminate [] xx’] >>
  gvs[init_st_def]>>
  pop_assum $ irule_at Any >>
  xsimpl
QED

(* semantics theorem about whole program *)

(*
  max_print_depth := 35
*)

val Decls_thm =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def,ml_progTheory.ML_code_env_def];

Definition update_oracle_def:
  update_oracle =
    ((λfname st a1 a2.
        case fname of
        | SharedMem _ => Oracle_final FFI_failed
        | ExtCall n   => case update n a1 a2 st of
                         | SOME (FFIreturn x y) => Oracle_return y x
                         | _ => Oracle_final FFI_failed) : ffi oracle)
End

Definition custom_ffi_def:
  custom_ffi s =
    <| oracle    := update_oracle
     ; ffi_state := s
     ; io_events := []
   |>
End

Definition ffi_proj_def:
  ffi_proj (s:ffi) = FEMPTY |++ (MAP (λn. (n,s)) names)
End

Theorem parts_ok_custom_ffi:
  parts_ok (custom_ffi s) (ffi_proj,[(names,update)])
Proof
  rw [cfStoreTheory.parts_ok_def]
  >- EVAL_TAC >- EVAL_TAC
  >- (gvs [ffi_proj_def,custom_ffi_def,FLOOKUP_FUPDATE_LIST] >>
      qexists_tac ‘s’ >> fs [])
  >- (gvs [custom_ffi_def,update_oracle_def] >>
      gvs [update_def,AllCaseEqs(), oneline update_step_def, oneline update_clause_def,
           oneline update_hints_def,LENGTH_write_bytes,
           oneline update_callback_def])
  >- (gvs [update_def,AllCaseEqs(), oneline update_step_def, oneline update_clause_def,
           oneline update_hints_def,LENGTH_write_bytes,
           oneline update_callback_def]) >>
  ‘ffi_proj x ' m = x’ by
   (qsuff_tac ‘FLOOKUP (ffi_proj x) m = SOME x’ >- simp [FLOOKUP_DEF] >>
    fs [FLOOKUP_FUPDATE_LIST, ffi_proj_def]) >>
  fs [custom_ffi_def,update_oracle_def] >>
  gvs [TO_FLOOKUP,FLOOKUP_FUPDATE_LIST,FUN_EQ_THM] >>
  rw [] >> fs [FLOOKUP_FUPDATE_LIST, ffi_proj_def]
QED

Theorem SPLIT_heaps_lemma[local]:
  SPLIT
    (store2heap (distrup_arrayProg_st (custom_ffi s)).refs ∪
     ffi2heap (ffi_proj,[(names,update)]) (distrup_arrayProg_st (custom_ffi s)).ffi)
    ({FFI_part s update names []},
     FFI_split INSERT store2heap (distrup_arrayProg_st (custom_ffi s)).refs)
Proof
  fs [EVAL “(distrup_arrayProg_st ffi).ffi”] >>
  qsuff_tac
    ‘ffi2heap (ffi_proj,[(names,update)]) (custom_ffi s) =
     {FFI_split; FFI_part s update names []}’
  >-
   (strip_tac >> simp [SPLIT_def] >>
    conj_tac >- (gvs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ gvs []) >>
    gvs [cfAppTheory.FFI_part_NOT_IN_store2heap]) >>
  simp [cfStoreTheory.ffi2heap_def] >>
  gvs [parts_ok_custom_ffi] >>
  fs [EVAL “(distrup_arrayProg_st ffi).ffi”,
      EVAL “(custom_ffi s).ffi_state”,
      EVAL “(custom_ffi s).io_events”, SF CONJ_ss] >>
  ‘∀n. MEM n names ⇒ FLOOKUP (ffi_proj s) n = SOME s’ by
     gvs [ffi_proj_def,FLOOKUP_FUPDATE_LIST] >>
  gvs [] >>
  simp [EXTENSION] >> rw [] >> eq_tac >> rw [] >>
  gvs [names_def,SF DNF_ss]
QED

val main_lemma = main_spec
  |> SRULE [app_def,app_basic_def,cfHeapsBaseTheory.POSTv_ignore,PULL_EXISTS]
  |> SRULE [CUSTOM_FFI_def,SEP_EXISTS,PULL_EXISTS,cond_STAR]
  |> SRULE [one_def,evaluate_to_heap_def,PULL_EXISTS]
  |> SRULE [cfStoreTheory.st2heap_def]
  |> Q.GEN ‘p’ |> Q.ISPEC ‘ffi_proj,[(names,update)]’
  |> Q.SPECL [‘hhh’,‘distrup_arrayProg_st ffi’]
  |> Q.GEN ‘ffi’ |> Q.SPEC ‘custom_ffi (State Step inputs tb)’
  |> C MATCH_MP (SPLIT_heaps_lemma |> Q.GEN ‘s’ |> Q.SPEC ‘State Step inputs tb’)
  |> Q.GEN ‘inputs’
  |> Q.GEN ‘tb’
  |> SRULE [boolTheory.SKOLEM_THM]

val main_res = new_specification("main_res",
  ["main_env","main_exp","main_h","main_res","main_events","main_ck","main_st"],
  main_lemma);

Theorem FILTER_SKIP:
  ∀xs P. EVERY P xs ⇒ FILTER P xs = xs
Proof
  Induct \\ gvs []
QED

Theorem main_st_ffi_events:
  (main_st tb inputs).ffi.io_events = main_events tb inputs
Proof
  assume_tac (main_res |> SPEC_ALL |> cj 1) >>
  gvs [SPLIT3_def] >>
  last_x_assum mp_tac >>
  simp [SET_EQ_SUBSET,cfStoreTheory.FFI_part_NOT_IN_store2heap] >>
  strip_tac >>
  fs [cfStoreTheory.ffi2heap_def] >>
  Cases_on ‘parts_ok (main_st tb inputs).ffi (ffi_proj,[(names,update)])’ >> gvs [] >>
  pop_assum mp_tac >>
  rpt $ pop_assum kall_tac >>
  rw [cfStoreTheory.parts_ok_def] >>
  DEP_REWRITE_TAC [FILTER_SKIP] >> simp []
QED

val ml_code_thm = get_ml_prog_state () |> get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def,ml_progTheory.Decls_def,ml_progTheory.ML_code_env_def]
  |> cj 2;

Theorem semantics_prog_distrup_prog:
  semantics_prog (init_state (custom_ffi (State Step inputs tb))) init_env
    distrup_prog
    (Terminate Success (main_events tb inputs))
Proof
  gvs [semanticsTheory.semantics_prog_def] >>
  qrefinel [‘_’,‘_’,‘Rval v’] >> simp [] >>
  qspec_then ‘custom_ffi (State Step inputs tb)’ strip_assume_tac (ml_code_thm |> Q.GEN ‘ffi’) >>
  pop_assum mp_tac >>
  qmatch_goalsub_abbrev_tac ‘p:dec list’ >>
  ‘distrup_prog = SNOC ^main_call p’ by (unabbrev_all_tac >> EVAL_TAC) >>
  DEP_REWRITE_TAC [evaluate_decTheory.evaluate_dec_list_eq_evaluate_decs] >>
  conj_tac >- (unabbrev_all_tac >> EVAL_TAC) >>
  last_x_assum kall_tac >> simp [] >>
  last_x_assum kall_tac >> rw [] >>
  fs [semanticsTheory.evaluate_prog_with_clock_def,SNOC_APPEND] >>
  qspecl_then [‘tb’,‘inputs’] mp_tac main_res >>
  strip_tac >>
  simp [evaluatePropsTheory.evaluate_decs_append] >>
  drule evaluatePropsTheory.evaluate_decs_set_clock >> simp [] >>
  disch_then $ qspec_then ‘main_ck tb inputs + 1’ mp_tac >> strip_tac >>
  rename [‘init_state (custom_ffi (State Step inputs tb)) with clock := ck4’] >>
  qrefinel [‘_’,‘ck4’] >> fs [] >>
  fs [evaluateTheory.evaluate_decs_def,astTheory.pat_bindings_def,
      evaluateTheory.evaluate_def,semanticPrimitivesTheory.build_conv_def,
      semanticPrimitivesTheory.do_con_check_def] >>
  simp [semanticPrimitivesTheory.extend_dec_env_def] >>
  CONV_TAC (DEPTH_CONV nsLookup_conv) >> simp [] >>
  qpat_x_assum ‘SOME _ = _’ $ assume_tac o GSYM >>
  asm_rewrite_tac [] >> simp [] >>
  fs [evaluateTheory.dec_clock_def,cfAppTheory.evaluate_ck_def] >>
  simp [semanticPrimitivesTheory.pmatch_def] >>
  simp [semanticPrimitivesTheory.combine_dec_result_def] >>
  simp [main_st_ffi_events]
QED

Theorem full_events_ok_main_events:
  full_events_ok init_st (main_events tb inputs)
Proof
  gvs [main_res]
QED
