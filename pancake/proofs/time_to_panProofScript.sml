(*
  Correctness proof for timeLang to panLang
*)

open preamble
     timeSemTheory panSemTheory
     timePropsTheory panPropsTheory
     pan_commonPropsTheory time_to_panTheory
     timeFunSemTheory


val _ = new_theory "time_to_panProof";

val _ = set_grammar_ancestry
        ["timeSem", "panSem",
         "pan_commonProps", "timeProps",
         "time_to_pan"];

val _ = temp_delsimps ["OPT_MMAP_def"];

(*
  FFI abstraction
*)

Type time_input = ``:num -> num # num``

Type time_input_ffi = ``:time_input ffi_state``

Type pan_state = ``:('a, time_input) panSem$state``


Definition get_bytes_def:
  get_bytes be (w:'a word) =
  let m  = dimindex (:'a) DIV 8;
      as = GENLIST (λm. (n2w m): 'a word) m
  in
    MAP (λa. get_byte a w be) as
End


Definition time_input_def:
  time_input (:'a) be (f:num -> num # num) =
  let
    t = n2w (FST (f 1)):'a word;
    b = n2w (SND (f 1)):'a word;
  in
    get_bytes be t ++
    get_bytes be b
End


Definition next_ffi_def:
  next_ffi (f:num -> (num # num)) =
    λn. f (n+1)
End


Definition string_to_word_def:
  string_to_word =
    n2w o THE o fromNatString o implode
End


Definition build_ffi_def:
  build_ffi (:'a) be outs (seq:time_input) io =
     <| oracle    :=
        (λs f conf bytes.
          if s = "get_time_input"
          then Oracle_return (next_ffi f) (time_input (:'a) be f)
          else if MEM s outs
          then Oracle_return f bytes
          else Oracle_final FFI_failed)
      ; ffi_state := seq
      ; io_events := io|> : time_input_ffi
End

(* End of FFI abstraction *)

Definition equiv_val_def:
  equiv_val fm xs v <=>
    v = MAP (ValWord o n2w o THE o (FLOOKUP fm)) xs
End


Definition valid_clks_def:
  valid_clks clks tclks wt <=>
    EVERY (λck. MEM ck clks) tclks ∧
    EVERY (λck. MEM ck clks) (MAP SND wt)
End


Definition resetClksVals_def:
  resetClksVals fm xs ys  =
    MAP
    (ValWord o n2w o THE o
     (FLOOKUP (resetClocks fm ys))) xs
End


Definition retVal_def:
  retVal s clks tclks wt dest =
    Struct [
        Struct (resetClksVals s.clocks clks tclks);
        ValWord (case wt of [] => 1w | _ => 0w);
        ValWord (case wt of [] => 0w
                         | _ => n2w (THE (calculate_wtime s tclks wt)));
        ValLabel (num_to_str dest)]
End


Definition maxClksSize_def:
  maxClksSize clks ⇔
    SUM (MAP (size_of_shape o shape_of) clks) ≤ 29
End


Definition defined_clocks_def:
  defined_clocks fm clks ⇔
    EVERY
      (λck. ∃n. FLOOKUP fm ck = SOME n) clks
End


Definition clock_bound_def:
  clock_bound fm clks (m:num) ⇔
    EVERY
      (λck. ∃n. FLOOKUP fm ck = SOME n ∧
                n < m) clks
End

Definition restore_from_def:
  (restore_from t lc [] = lc) ∧
  (restore_from t lc (v::vs) =
   restore_from t (res_var lc (v, FLOOKUP t.locals v)) vs)
End

Definition emptyVals_def:
  emptyVals n = REPLICATE n (ValWord 0w)
End

Definition constVals_def:
  constVals n v = REPLICATE n v
End


Definition minOption_def:
  (minOption (x:'a word) NONE = x) ∧
  (minOption x (SOME (y:num)) =
    if x <₊ n2w y then x else n2w y)
End


Definition well_behaved_ffi_def:
  well_behaved_ffi ffi_name (s:(α, β) panSem$state) n (m:num) <=>
  explode ffi_name ≠ "" ∧ n < m ∧
  ∃bytes.
    read_bytearray s.base_addr n
                   (mem_load_byte s.memory s.memaddrs s.be) =
    SOME bytes ∧
    s.ffi.oracle (explode ffi_name) s.ffi.ffi_state [] bytes =
    Oracle_return s.ffi.ffi_state bytes
End


Definition ffi_return_state_def:
  ffi_return_state s ffi_name bytes =
  s with
    <|memory := write_bytearray s.base_addr bytes s.memory s.memaddrs s.be;
      ffi :=
      s.ffi with
       <|io_events :=
         s.ffi.io_events ++
          [IO_event (explode ffi_name) [] (ZIP (bytes,bytes))]|> |>
End


Definition nffi_state_def:
  nffi_state s (n:num) bytes =
    s.ffi with
     <|io_events :=
       s.ffi.io_events ++
        [IO_event (explode (num_to_str n)) [] (ZIP (bytes,bytes))]|>
End

Definition code_installed_def:
  code_installed code prog <=>
  ∀loc tms.
    MEM (loc,tms) prog ⇒
    let clks = clksOf prog;
        n = LENGTH clks
    in
      FLOOKUP code (num_to_str loc) =
      SOME ([(«clks», genShape n);
             («event», One)],
            compTerms clks «clks» «event» tms)
End


Definition ffi_vars_def:
  ffi_vars fm ba ⇔
  FLOOKUP fm «ptr1» = SOME (ValWord 0w) ∧
  FLOOKUP fm «len1» = SOME (ValWord 0w) ∧
  FLOOKUP fm «ptr2» = SOME (ValWord ba) ∧
  FLOOKUP fm «len2» = SOME (ValWord ffiBufferSize)
End


Definition time_vars_def:
  time_vars fm ⇔
  (∃st. FLOOKUP fm «sysTime»  = SOME (ValWord st)) ∧
  (∃wt. FLOOKUP fm «wakeUpAt» = SOME (ValWord wt)) ∧
  (∃io. FLOOKUP fm «event»    = SOME (ValWord io)) ∧
  (∃i.  FLOOKUP fm «isInput»  = SOME (ValWord i)) ∧
  (∃w.  FLOOKUP fm «waitSet»  = SOME (ValWord w))
End


(* for easier reasoning *)
Definition clkvals_rel_def:
  clkvals_rel fm xs ys (n:num) ⇔
    MAP (λ(x,y). y + THE (FLOOKUP fm x)) (ZIP (xs,ys)) =
    MAP (λx. n) ys ∧
    EVERY (\x. THE (FLOOKUP fm x) <= n) xs
End


Definition clocks_rel_def:
  clocks_rel sclocks tlocals clks stime ⇔
  ∃ns.
    FLOOKUP tlocals «clks» =
    SOME (Struct (MAP (ValWord o n2w) ns)) ∧
    LENGTH clks = LENGTH ns ∧
    clkvals_rel sclocks clks ns stime
End


Definition active_low_def:
  (active_low NONE = 1w) ∧
  (active_low (SOME _) = 0w)
End


Definition equivs_def:
  equivs fm loc wt ⇔
  FLOOKUP fm «loc» = SOME (ValLabel (num_to_str loc)) ∧
  FLOOKUP fm «waitSet» = SOME (ValWord (active_low wt))
End

Definition time_seq_def:
  time_seq (f:num -> num # num) m ⇔
  (∀n. ∃d. FST (f (SUC n)) = FST (f n) + d) ∧
  (∀n. FST (f n) < m)
End


Definition mem_config_def:
  mem_config (mem:'a word -> 'a word_lab) (adrs:('a word) set) be ba ⇔
    (∃w. mem ba = Word w) ∧
    (∃w. mem (ba + bytes_in_word) = Word w) ∧
    ba ∈ adrs ∧
    ba + bytes_in_word ∈ adrs
End


Definition has_input_def:
  has_input (n:num # num) ⇔ SND n ≠ 0
End


Definition input_time_eq_def:
  input_time_eq (n:num # num) m ⇔
   has_input m ⇒ FST m = FST n
End


Definition input_time_rel_def:
  input_time_rel (f:num -> num # num) ⇔
    !n. input_time_eq (f n) (f (n+1))
End


Definition state_rel_def:
  state_rel clks outs s (t:('a,time_input) panSem$state) ⇔
    equivs t.locals s.location s.waitTime ∧
    ffi_vars t.locals t.base_addr ∧  time_vars t.locals ∧
    mem_config t.memory t.memaddrs t.be t.base_addr ∧
    LENGTH clks ≤ 29 ∧ byte_align t.base_addr = t.base_addr ∧
    defined_clocks s.clocks clks ∧
    let
      ffi = t.ffi.ffi_state;
      io_events = t.ffi.io_events;
      (tm,io_flg) = ffi 0
    in
      t.ffi = build_ffi (:'a) t.be (MAP explode outs) ffi io_events ∧
      input_time_rel ffi ∧
      time_seq ffi (dimword (:'a)) ∧
      FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w tm)) ∧
      clocks_rel s.clocks t.locals clks tm
End

Definition nexts_ffi_def:
  nexts_ffi m (f:num -> (num # num)) =
  λn. f (n+m)
End


Definition delay_rep_def:
  delay_rep (d:num) (seq:time_input) cycles ⇔
    FST (seq cycles) = d + FST (seq 0) ∧
    ∀i. i ≤ cycles ⇒ SND (seq i) = 0
End

Definition wakeup_rel_def:
  (wakeup_rel fm NONE _ (seq:time_input) cycles = T) ∧
  (wakeup_rel fm (SOME wt) ist seq cycles =
   let
     st =  FST (seq 0);
     swt = ist + wt
   in
     FLOOKUP fm «sysTime»  = SOME (ValWord (n2w st)) ∧
     ist ≤ st ∧
     FLOOKUP fm «wakeUpAt» = SOME (ValWord (n2w swt)) ∧
     (∀i. i ≤ cycles ⇒
          FST (seq i) < swt))
End


Definition conds_clks_mem_clks_def:
  conds_clks_mem_clks clks tms =
    EVERY (λtm.
            EVERY (λcnd.
                    EVERY (λck. MEM ck clks) (condClks cnd))
                  (termConditions tm)
          ) tms
End

Definition terms_valid_clocks_def:
  terms_valid_clocks clks tms  =
    EVERY (λtm.
            valid_clks clks (termClks tm) (termWaitTimes tm)
          ) tms
End

Definition locs_in_code_def:
  locs_in_code fm tms =
    EVERY (λtm.
            num_to_str (termDest tm) IN FDOM fm
          ) tms
End


Definition out_signals_ffi_def:
  out_signals_ffi (t :('a, 'b) panSem$state) tms =
    EVERY (λout.
            well_behaved_ffi (num_to_str out) t
                             (w2n (ffiBufferSize:'a word)) (dimword (:α)))
          (terms_out_signals tms)
End


Definition mem_call_ffi_def:
  mem_call_ffi (:α) mem adrs be ba (ffi: (num -> num # num)) =
    write_bytearray
    ba
    (get_bytes be ((n2w (FST (ffi 1))):'a word) ++
     get_bytes be ((n2w (SND (ffi 1))):'a word))
    mem adrs be
End


Definition ffi_call_ffi_def:
  ffi_call_ffi (:α) be ffi bytes =
    ffi with
        <|ffi_state := next_ffi ffi.ffi_state;
          io_events := ffi.io_events ++
          [IO_event "get_time_input" []
           (ZIP
            (bytes,
             get_bytes be ((n2w (FST (ffi.ffi_state (1:num)))):'a word) ++
             get_bytes be ((n2w (SND (ffi.ffi_state 1))):'a word)))]|>

End


Datatype:
  observed_io = ObsTime    num
              | ObsInput   num
              | ObsOutput  num
End


Definition to_label_def:
  (to_label (ObsTime n)   = LDelay n) ∧
  (to_label (ObsInput n)  = LAction (Input n)) ∧
  (to_label (ObsOutput n) = LAction (Output n))
End


Definition to_delay_def:
  (to_delay (ObsTime n) = SOME n) ∧
  (to_delay _  = NONE)
End


Definition to_input_def:
  (to_input (ObsInput n) = SOME (Input (n - 1))) ∧
  (to_input _  = NONE)
End

Definition mem_read_ffi_results_def:
  mem_read_ffi_results  (:'a) ffi (cycles:num) ⇔
  ∀i (t:('a,time_input) panSem$state) (t':('a,time_input) panSem$state).
    i < cycles ∧
    t.ffi.ffi_state = nexts_ffi i ffi ∧
    evaluate
    (ExtCall «get_time_input» «ptr1» «len1» «ptr2» «len2» , t) =
    (NONE,t') ⇒
    t'.memory t'.base_addr =
    Word (n2w (FST (nexts_ffi i ffi 1))) ∧
    t'.memory (bytes_in_word + t'.base_addr) =
    Word (n2w (SND (nexts_ffi i ffi 1)))
End

Definition io_event_dest_def:
  io_event_dest (:'a) be (IO_event _ _ l) =
  (MAP w2n o
   (words_of_bytes: bool -> word8 list -> α word list) be o
   MAP SND) l
End

Definition io_events_dest_def:
  io_events_dest (:'a) be ios =
    MAP (io_event_dest (:'a) be) ios
End


Definition from_io_events_def:
  from_io_events (:'a) be n ys =
    io_events_dest (:'a) be (DROP n ys)
End


Definition decode_io_event_def:
  decode_io_event (:'a) be (IO_event s conf l) =
    if s ≠ "get_time_input" then (ObsOutput (toNum s))
    else (
      let
        ti = io_event_dest (:'a) be (IO_event s conf l);
        time  = EL 0 ti;
        input = EL 1 ti
      in
        if input = 0 then (ObsTime time)
        else (ObsInput input))
End

Definition decode_io_events_def:
  decode_io_events (:'a) be ios =
    MAP (decode_io_event (:'a) be) ios
End


Definition io_events_eq_ffi_seq_def:
  io_events_eq_ffi_seq seq cycles xs ⇔
  LENGTH xs = cycles ∧
  EVERY (λx. LENGTH x = 2) xs ∧
  (∀i. i < cycles ⇒
       (EL 0 (EL i xs), EL 1 (EL i xs)) = seq (i+1))
End


Definition mk_ti_event_def:
  mk_ti_event (:α) be bytes seq =
    IO_event "get_time_input" []
             (ZIP (bytes, time_input (:α) be seq))
End


Definition mk_ti_events_def:
  mk_ti_events (:α) be (bytess:word8 list list) seqs =
    MAP (λ(bytes,seq). mk_ti_event (:α) be bytes seq)
        (ZIP (bytess, seqs))
End

Definition gen_ffi_states_def:
  gen_ffi_states seq cycles =
    MAP (λm. (λn. seq (n + m)))
        (GENLIST I cycles)
End

Definition delay_io_events_rel_def:
  delay_io_events_rel (t:('a,time_input) panSem$state) (t':('a,time_input) panSem$state) cycles ⇔
  let
    n = LENGTH t.ffi.io_events;
    ios_to_nums = from_io_events (:'a) t.be n t'.ffi.io_events;
    nios = DROP n t'.ffi.io_events;
    obs_ios = decode_io_events (:'a) t'.be nios;
  in
    (∃bytess.
       LENGTH bytess = cycles ∧
       EVERY (λbtyes. LENGTH btyes = 2 * dimindex (:α) DIV 8) bytess ∧
       t'.ffi.io_events =
       t.ffi.io_events ++
        mk_ti_events (:α) t'.be bytess (gen_ffi_states t.ffi.ffi_state cycles)) ∧
    io_events_eq_ffi_seq t.ffi.ffi_state cycles ios_to_nums ∧
    (∀n. n < LENGTH obs_ios ⇒
         EL n obs_ios = ObsTime (FST (t.ffi.ffi_state (n+1))))
End

Definition delay_ios_mono_def:
  delay_ios_mono obs_ios seq ⇔
  ∀i j.
    i < LENGTH obs_ios ∧ j < LENGTH obs_ios ∧ i < j ⇒
    EL i obs_ios = ObsTime (FST (seq (i+1))) ∧
    EL j obs_ios = ObsTime (FST (seq (j+1))) ∧
    FST (seq (i+1)) ≤ FST (seq (j+1))
End


(* to remove cycles dependency *)
Definition obs_ios_are_label_delay_def:
  obs_ios_are_label_delay d (t:('a,time_input) panSem$state) (t':('a,time_input) panSem$state) ⇔
  let
    n = LENGTH t.ffi.io_events;
    nios = DROP n t'.ffi.io_events;
    obs_ios = decode_io_events (:'a) t'.be nios;
  in
    delay_ios_mono obs_ios t.ffi.ffi_state ∧
    (obs_ios ≠ [] ⇒
     LDelay d = LDelay (THE (to_delay (EL (LENGTH obs_ios - 1) obs_ios)) -
                        EL 0 (io_event_dest (:α) t.be (LAST t.ffi.io_events))))
End


Definition well_formed_terms_def:
  well_formed_terms prog loc code <=>
  ∀tms.
    ALOOKUP prog loc = SOME tms ⇒
    conds_clks_mem_clks (clksOf prog) tms ∧
    terms_valid_clocks (clksOf prog) tms ∧ locs_in_code code tms
End


(* should stay as an invariant *)
Definition task_ret_defined_def:
  task_ret_defined (fm: mlstring |-> 'a v) n ⇔
  ∃(vs:'a v list) v1 v2 v3.
    FLOOKUP fm «taskRet» = SOME (
      Struct [
          Struct vs;
          ValWord v1;
          ValWord v2;
          ValLabel v3
        ]) ∧
    EVERY (λv. ∃w. v = ValWord w) vs ∧
    LENGTH vs = n
End

Definition input_rel_def:
  input_rel fm n seq =
   let
     st = FST (seq (0:num));
     input  = SND (seq 0)
   in
     FLOOKUP fm «sysTime»  = SOME (ValWord (n2w st)) ∧
     FLOOKUP fm «event» = SOME (ValWord (n2w input)) ∧
     n = input - 1 ∧ input <> 0
End

Definition wakeup_rel_def:
  (wakeup_rel fm NONE _ (seq:time_input) cycles = T) ∧
  (wakeup_rel fm (SOME wt) ist seq cycles =
   let
     st =  FST (seq 0);
     swt = ist + wt
   in
     FLOOKUP fm «sysTime»  = SOME (ValWord (n2w st)) ∧
     ist ≤ st ∧
     FLOOKUP fm «wakeUpAt» = SOME (ValWord (n2w swt)) ∧
     (∀i. i ≤ cycles ⇒
          FST (seq i) < swt))
End

Definition wakeup_shape_def:
  wakeup_shape (fm: mlstring |-> 'a v) wt ist ⇔
  ∃wt'.
    FLOOKUP fm «wakeUpAt» = SOME (ValWord (n2w (ist + wt'))) ∧
    wt' < dimword (:α) - 1 ∧
    (case wt of
     | NONE => T
     | SOME wt => wt ≤ wt')
End


Definition wait_time_locals1_def:
  wait_time_locals1 (:α) fm swt ist nst =
  ∃wt.
    FLOOKUP fm «wakeUpAt» = SOME (ValWord (n2w (wt + ist))) ∧
    wt < dimword (:α) - 1 ∧
    case swt of
    | NONE => T
    | SOME swt =>
        swt ≠ 0:num ⇒
        nst < wt + ist
End


Definition input_stime_rel_def:
  (input_stime_rel NONE _ _ ⇔ T) ∧
  (input_stime_rel (SOME (wt:num)) ist st ⇔
   ist ≤ st ∧
   st < ist + wt)
End


Definition input_eq_ffi_seq_def:
  input_eq_ffi_seq (seq:num -> num # num) xs ⇔
  LENGTH xs = 2 ∧
  (EL 0 xs, EL 1 xs) = seq 1
End


Definition input_io_events_rel_def:
  input_io_events_rel i (t:('a,time_input) panSem$state) (t':('a,time_input) panSem$state) ⇔
  let
    n = LENGTH t.ffi.io_events;
    nios = DROP n t'.ffi.io_events;
    ios_to_nums = from_io_events (:'a) t.be n t'.ffi.io_events;
    obs_ios = decode_io_events (:'a) t'.be nios
  in
  (∃bytes.
     LENGTH bytes = 2 * dimindex (:α) DIV 8 ∧
     t'.ffi.io_events =
     t.ffi.io_events ++
      [mk_ti_event (:α) t'.be bytes t.ffi.ffi_state]) ∧
  (∃ns.
     ios_to_nums = [ns] ∧
     input_eq_ffi_seq t.ffi.ffi_state ns) ∧
  LENGTH obs_ios = 1 ∧
  EL 0 obs_ios = ObsInput (SND (t.ffi.ffi_state 1)) ∧
  LAction (Input i) = LAction (THE (to_input (EL 0 obs_ios)))
End


Definition output_rel_def:
  output_rel fm (seq: num -> num # num) =
  let
    st = FST (seq 0)
  in
    ∃wt nt.
      FLOOKUP fm «sysTime»  = SOME (ValWord (n2w st)) ∧
      FLOOKUP fm «wakeUpAt» = SOME (ValWord (n2w (wt + nt))) ∧
      st = wt + nt ∧
      SND (seq 0) = 0
End

Definition output_io_events_rel_def:
  output_io_events_rel os (t:('a,time_input) panSem$state) (t':('a,time_input) panSem$state) ⇔
  let
    n = LENGTH t.ffi.io_events;
    nios = DROP n t'.ffi.io_events;
    obs_ios = decode_io_events (:'a) t'.be nios
  in
    (∃(bytes:word8 list).
       t'.ffi.io_events =
       t.ffi.io_events ++
        [IO_event (explode (num_to_str os)) [] (ZIP (bytes, bytes))]) ∧
    obs_ios = [ObsOutput os]
End

Definition well_formed_code_def:
  well_formed_code prog code <=>
  ∀loc tms.
    ALOOKUP prog loc = SOME tms ⇒
    well_formed_terms prog loc code
End


Definition event_inv_def:
  event_inv fm ⇔
    FLOOKUP fm «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP fm «event» = SOME (ValWord 0w)
End

Definition assumptions_def:
  assumptions prog n s (t:('a,time_input) panSem$state) ⇔
    state_rel (clksOf prog) (out_signals prog) s t ∧
    code_installed t.code prog ∧
    well_formed_code prog t.code ∧
    n = FST (t.ffi.ffi_state 0) ∧
    good_dimindex (:'a) ∧
    ~MEM "get_time_input" (MAP explode (out_signals prog)) ∧
    event_inv t.locals ∧
    task_ret_defined t.locals (nClks prog) ∧
    FLOOKUP t.eshapes «panic» = SOME One
End


Definition evaluations_def:
  (evaluations prog [] [] ist s (t:('a,time_input) panSem$state) ⇔ T) ∧
  (evaluations prog (lbl::lbls) (st::sts) ist s t ⇔
     case lbl of
     | LDelay d =>
         evaluate_delay prog d ist s st t lbls sts
     | LAction act =>
        (case act of
         | Input i =>
             evaluate_input prog i s st t lbls sts
         | Output os =>
             evaluate_output prog os st t lbls sts)
     | LPanic panic =>
         case panic of
         | PanicTimeout =>
             (output_rel t.locals t.ffi.ffi_state ∧
              FST (t.ffi.ffi_state 0) < dimword (:α) - 2 ⇒
              ∃ck nt.
                (∀ck_extra.
                   evaluate (time_to_pan$always (nClks prog), t with clock := t.clock + ck + ck_extra) =
                   (SOME (Exception «panic» (ValWord 0w)), nt with clock := nt.clock + ck_extra)) ∧
                nt.code = t.code ∧
                nt.be = t.be ∧ nt.base_addr = t.base_addr ∧
                nt.ffi.ffi_state = t.ffi.ffi_state ∧
                nt.ffi.io_events = t.ffi.io_events ∧
                nt.ffi.oracle = t.ffi.oracle ∧
                nt.eshapes = t.eshapes)
         | PanicInput i =>
             (wakeup_shape t.locals s.waitTime (FST (t.ffi.ffi_state 0)) ∧
              input_stime_rel s.waitTime (FST (t.ffi.ffi_state 0)) (FST (t.ffi.ffi_state 0)) ∧
              input_rel t.locals i (next_ffi t.ffi.ffi_state) ∧
              mem_read_ffi_results (:α) t.ffi.ffi_state 1 ∧
              FST (t.ffi.ffi_state 1) < dimword (:α) - 2 ⇒
              ∃ck nt.
                (∀ck_extra.
                   evaluate (time_to_pan$always (nClks prog), t with clock := t.clock + ck + ck_extra) =
                   (SOME (Exception «panic» (ValWord 0w)), nt with clock := nt.clock + ck_extra)) ∧
                ~MEM "get_time_input" (MAP explode (out_signals prog)) ∧
                nt.code = t.code ∧
                nt.be = t.be ∧ nt.base_addr = t.base_addr ∧
                nt.ffi.ffi_state = next_ffi t.ffi.ffi_state ∧
                nt.ffi.oracle = t.ffi.oracle ∧
                nt.eshapes = t.eshapes ∧
                nt.locals = FEMPTY ∧
                input_io_events_rel i t nt)) ∧

  (evaluate_delay prog d ist s st (t:('a,time_input) panSem$state) lbls sts ⇔
   ∀cycles.
     delay_rep d t.ffi.ffi_state cycles ∧
     wakeup_shape t.locals s.waitTime ist ∧
     wakeup_rel t.locals s.waitTime ist t.ffi.ffi_state cycles ∧
     mem_read_ffi_results (:α) t.ffi.ffi_state cycles ∧
     t.ffi.io_events ≠ [] ∧
     EL 0 (io_event_dest (:α) t.be (LAST t.ffi.io_events)) = FST (t.ffi.ffi_state 0) ⇒
     ∃ck nt.
       (∀ck_extra.
          evaluate (time_to_pan$always (nClks prog), t with clock := t.clock + ck + ck_extra) =
          evaluate (time_to_pan$always (nClks prog), nt with clock := nt.clock + ck_extra)) ∧
       state_rel (clksOf prog) (out_signals prog) st nt ∧
       ~MEM "get_time_input" (MAP explode (out_signals prog)) ∧
       event_inv nt.locals ∧
       nt.code = t.code ∧
       nt.be = t.be ∧ nt.base_addr = t.base_addr ∧
       nt.ffi.ffi_state = nexts_ffi cycles t.ffi.ffi_state ∧
       nt.ffi.oracle = t.ffi.oracle ∧
       nt.eshapes = t.eshapes ∧
       FLOOKUP nt.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt» ∧
       FLOOKUP nt.locals «waitSet» = FLOOKUP t.locals «waitSet» ∧
       FLOOKUP nt.locals «taskRet» = FLOOKUP t.locals «taskRet» ∧
       FLOOKUP nt.locals «sysTime»  =
       SOME (ValWord (n2w (FST (t.ffi.ffi_state cycles)))) ∧
       wait_time_locals1 (:α) nt.locals st.waitTime ist (FST (nt.ffi.ffi_state 0)) ∧
       delay_io_events_rel t nt cycles ∧
       obs_ios_are_label_delay d t nt ∧
       task_ret_defined nt.locals (nClks prog) ∧
       evaluations prog lbls sts ist st nt) ∧

  (evaluate_input prog i s st (t:('a,time_input) panSem$state) lbls sts ⇔
   wakeup_shape t.locals s.waitTime (FST (t.ffi.ffi_state 0)) ∧
   input_stime_rel s.waitTime (FST (t.ffi.ffi_state 0)) (FST (t.ffi.ffi_state 0)) ∧
   input_rel t.locals i (next_ffi t.ffi.ffi_state) ∧
   mem_read_ffi_results (:α) t.ffi.ffi_state 1 ∧
   FST (t.ffi.ffi_state 1) < dimword (:α) - 2 ⇒
   ∃ck nt.
     (∀ck_extra.
        evaluate (time_to_pan$always (nClks prog), t with clock := t.clock + ck + ck_extra) =
        evaluate (time_to_pan$always (nClks prog), nt with clock := nt.clock + ck_extra)) ∧
     state_rel (clksOf prog) (out_signals prog) st nt ∧
     ~MEM "get_time_input" (MAP explode (out_signals prog)) ∧
     event_inv nt.locals ∧
     nt.code = t.code ∧
     nt.be = t.be ∧ nt.base_addr = t.base_addr ∧
     nt.ffi.ffi_state = next_ffi t.ffi.ffi_state ∧
     nt.ffi.oracle = t.ffi.oracle ∧
     nt.eshapes = t.eshapes ∧
     FLOOKUP nt.locals «wakeUpAt» =
     SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) +
                         case st.waitTime of
                         | NONE => 0
                         | SOME wt => wt))) ∧
     FLOOKUP nt.locals «waitSet» =
     SOME (ValWord (n2w (
                     case st.waitTime of
                     | NONE => 1
                     | _ => 0))) ∧
     FLOOKUP nt.locals «sysTime» = FLOOKUP t.locals «sysTime» ∧
     wait_time_locals1 (:α) nt.locals st.waitTime (FST (t.ffi.ffi_state 0)) (FST (nt.ffi.ffi_state 0)) ∧
     input_io_events_rel i t nt ∧
     task_ret_defined nt.locals (nClks prog) ∧
     evaluations prog lbls sts (FST (t.ffi.ffi_state 0)) st nt) ∧

  (evaluate_output prog os st (t:('a,time_input) panSem$state) lbls sts ⇔
   output_rel t.locals t.ffi.ffi_state ∧
   FST (t.ffi.ffi_state 0) < dimword (:α) - 2 ⇒
   ∃ck nt.
     (∀ck_extra.
        evaluate (time_to_pan$always (nClks prog), t with clock := t.clock + ck + ck_extra) =
        evaluate (time_to_pan$always (nClks prog), nt with clock := nt.clock + ck_extra)) ∧
     state_rel (clksOf prog) (out_signals prog) st nt ∧
     ~MEM "get_time_input" (MAP explode (out_signals prog)) ∧
     event_inv nt.locals ∧
     nt.code = t.code ∧
     nt.be = t.be ∧ nt.base_addr = t.base_addr ∧
     nt.ffi.ffi_state = t.ffi.ffi_state ∧
     nt.ffi.oracle = t.ffi.oracle ∧
     nt.eshapes = t.eshapes ∧
     FLOOKUP nt.locals «wakeUpAt» =
     SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) +
                         case st.waitTime of
                         | NONE => 0
                         | SOME wt => wt))) ∧
     FLOOKUP nt.locals «waitSet» =
     SOME (ValWord (n2w (
                     case st.waitTime of
                     | NONE => 1
                     | _ => 0))) ∧
     FLOOKUP nt.locals «sysTime» = FLOOKUP t.locals «sysTime» ∧
     wait_time_locals1 (:α) nt.locals st.waitTime (FST (t.ffi.ffi_state 0)) (FST (nt.ffi.ffi_state 0)) ∧
     output_io_events_rel os t nt ∧
     task_ret_defined nt.locals (nClks prog) ∧
     evaluations prog lbls sts (FST (t.ffi.ffi_state 0)) st nt)
Termination
  WF_REL_TAC ‘measure $ λx. case x of
    | INL (_,lbls,_)                           => 2 * LENGTH lbls
    | INR (INL (prog,d,ist,s,st,t,lbls,sts))   => 2 * LENGTH lbls + 1
    | INR (INR (INL (prog,i,s,st,t,lbls,sts))) => 2 * LENGTH lbls + 1
    | INR (INR (INR (prog,os,st,t,lbls,sts)))  => 2 * LENGTH lbls + 1’
  \\ fs []
End


Definition action_rel_def:
  (action_rel (Input i) s (t:('a,time_input) panSem$state) ffi ⇔
    wakeup_shape t.locals s.waitTime (FST (t.ffi.ffi_state 0)) ∧
    input_stime_rel s.waitTime (FST (t.ffi.ffi_state 0)) (FST (t.ffi.ffi_state 0)) ∧
    input_rel t.locals i (next_ffi t.ffi.ffi_state) ∧
    mem_read_ffi_results (:α) t.ffi.ffi_state 1 ∧
    FST (t.ffi.ffi_state 1) < dimword (:α) − 2 ∧
    ffi = next_ffi t.ffi.ffi_state) ∧
  (action_rel (Output os) s t ffi ⇔
   output_rel t.locals t.ffi.ffi_state ∧
   FST (t.ffi.ffi_state 0) < dimword (:α) − 2 ∧
    ffi = t.ffi.ffi_state)
End

Definition panic_rel_def:
  (panic_rel PanicTimeout s (t:('a,time_input) panSem$state) ffi ⇔
   output_rel t.locals t.ffi.ffi_state ∧
   FST (t.ffi.ffi_state 0) < dimword (:α) - 2 ∧
   ffi = t.ffi.ffi_state) ∧
  (panic_rel (PanicInput i) s t ffi ⇔
   wakeup_shape t.locals s.waitTime (FST (t.ffi.ffi_state 0)) ∧
    input_stime_rel s.waitTime (FST (t.ffi.ffi_state 0)) (FST (t.ffi.ffi_state 0)) ∧
    input_rel t.locals i (next_ffi t.ffi.ffi_state) ∧
    mem_read_ffi_results (:α) t.ffi.ffi_state 1 ∧
    FST (t.ffi.ffi_state 1) < dimword (:α) − 2 ∧
    ffi = next_ffi t.ffi.ffi_state)
End


Definition ffi_rel_def:
  (ffi_rel (LDelay d) s (t:('a,time_input) panSem$state) ist ffi =
   ∃cycles.
     delay_rep d t.ffi.ffi_state cycles ∧
     wakeup_shape t.locals s.waitTime ist ∧
     wakeup_rel t.locals s.waitTime ist t.ffi.ffi_state cycles ∧
     mem_read_ffi_results (:α) t.ffi.ffi_state cycles ∧
     ffi = nexts_ffi cycles t.ffi.ffi_state ∧
     t.ffi.io_events ≠ [] ∧
     EL 0 (io_event_dest (:α) t.be (LAST t.ffi.io_events)) =
     FST (t.ffi.ffi_state 0)) ∧
  (ffi_rel (LAction act) s t ist ffi ⇔
   ist = FST (t.ffi.ffi_state 0) ∧
   action_rel act s t ffi) ∧
  (ffi_rel (LPanic p) s t ist ffi ⇔
   ist = FST (t.ffi.ffi_state 0) ∧
   panic_rel p s t ffi)
End

Definition ffi_rels_def:
  (ffi_rels prog [] s (t:('a,time_input) panSem$state) ist ⇔
   wait_time_locals1 (:α) t.locals s.waitTime ist (FST (t.ffi.ffi_state 0)) ∧
   ist < dimword (:α) − 1) ∧
  (ffi_rels prog (label::labels) s t ist ⇔
   ∃ffi.
     ffi_rel label s t ist ffi ∧
     ∀s' (t':('a,time_input) panSem$state) m n.
       step prog label m n s s' ∧
       t'.ffi.ffi_state = ffi ⇒
       ffi_rels prog labels s' t' ist)
End

(* TODO: change - to + :
         SUM (n::ns) + 1 = LENGTH ios *)
Definition decode_ios_def:
  (decode_ios (:α) be [] [] ios ⇔ LENGTH ios = 1) ∧
  (decode_ios (:α) be (lbl::lbls) (n::ns) ios ⇔
   SUM (n::ns) = LENGTH ios - 1 ∧
   (case lbl of
    | LDelay d =>
        (if n = 0
         then d = 0 ∧ decode_ios (:α) be lbls ns ios
         else
           let
             m' = EL 0 (io_event_dest (:α) be (HD ios));
             nios = TAKE n (TL ios);
             obs_ios = decode_io_events (:'a) be nios;
             m = THE (to_delay (EL (LENGTH obs_ios - 1) obs_ios))
           in
             d = m - m' ∧
             decode_ios (:α) be lbls ns (DROP n ios))
    | LAction act =>
        (n = 1 ∧
         decode_ios (:α) be lbls ns (DROP 1 ios) ∧
         (case act of
          | Input i =>
              let
                obs_io = decode_io_event (:α) be (EL 1 ios)
              in
                Input i = THE (to_input obs_io)
          | Output os =>
              decode_io_event (:α) be (EL 1 ios) = ObsOutput os))
    | LPanic p =>
        case p of
        | PanicInput i =>
            n = 1 ∧
            let
              obs_io = decode_io_event (:α) be (EL 1 ios)
            in
              Input i = THE (to_input obs_io)
        | _ => F)) ∧
  (decode_ios (:α) be _ _ ios ⇔ F)
End


Definition gen_max_times_def:
  (gen_max_times [] n ns = ns) ∧
  (gen_max_times (lbl::lbls) n ns =
   n ::
   let m =
       case lbl of
       | LDelay d => d + n
       | LAction _ => n
   in
   gen_max_times lbls m ns)
End

Definition init_clocks_def:
  init_clocks fm clks ⇔
    EVERY
      (λck. FLOOKUP fm ck = SOME (0:num)) clks
End

Definition init_ffi_def:
  init_ffi (f:num -> num # num) ⇔
    f 0 =  f 1 ∧
    SND (f 0) = 0
End


Definition locals_before_start_ctrl_def:
  locals_before_start_ctrl prog wt ffi ba =
  FEMPTY |+ («loc» ,ValLabel (toString (FST (ohd prog)))) |+
         («waitSet» ,
          ValWord (case wt of NONE => 1w | SOME v => 0w)) |+
         («event» ,ValWord 0w) |+ («isInput» ,ValWord 1w) |+
         («wakeUpAt» ,ValWord 0w) |+ («sysTime» ,ValWord 0w) |+
         («ptr1» ,ValWord 0w) |+ («len1» ,ValWord 0w) |+
         («ptr2» ,ValWord ba) |+
         («len2» ,ValWord ffiBufferSize) |+
         («taskRet» ,
          Struct
          [Struct (emptyVals (nClks prog)); ValWord 0w; ValWord 0w;
           ValLabel (toString (FST (ohd prog)))]) |+
         («clks» ,Struct (emptyVals (nClks prog))) |+
         («sysTime» ,ValWord (n2w (FST ffi))) |+
         («event» ,ValWord (n2w (SND ffi))) |+
         («isInput» ,ValWord 1w) |+
         («clks» ,
          Struct
          (REPLICATE (nClks prog)
           (ValWord (n2w (FST ffi))))) |+
         («wakeUpAt» ,
          ValWord
          (n2w
           (case wt of
              NONE => FST ffi
            | SOME n => n + FST ffi)))
End

Definition ffi_rels_after_init_def:
  ffi_rels_after_init prog labels st (t:('a,time_input) panSem$state) ⇔
  ∀bytes.
    read_bytearray t.base_addr (w2n (ffiBufferSize:'a word))
                   (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes ⇒
    ffi_rels prog labels st
             (t with
              <|locals :=
                locals_before_start_ctrl prog st.waitTime (t.ffi.ffi_state 0) t.base_addr;
                memory :=
                mem_call_ffi (:α) t.memory t.memaddrs t.be t.base_addr t.ffi.ffi_state;
                ffi := ffi_call_ffi (:α) t.be t.ffi bytes|>)
             (FST (t.ffi.ffi_state 0))
End


Definition labels_of_def:
  labels_of k prog m n or st =
   FST (THE (timeFunSem$eval_steps k prog m n or st))
End


Definition wf_prog_init_states_def:
  wf_prog_init_states prog or k st (t:('a,time_input) panSem$state) ⇔
    timeFunSem$eval_steps
    k prog (dimword (:α) - 1) (FST (t.ffi.ffi_state 0)) or st ≠ NONE ∧
    prog ≠ [] ∧ LENGTH (clksOf prog) ≤ 29 ∧
    st.location =  FST (ohd prog) ∧
    init_clocks st.clocks (clksOf prog) ∧
    code_installed t.code prog ∧
    FLOOKUP t.code «start» = SOME ([],ta_controller (prog,st.waitTime)) ∧
    FLOOKUP t.code «start_controller» =
    SOME ([],start_controller (prog,st.waitTime)) ∧
    FLOOKUP t.eshapes «panic» = SOME One ∧
    well_formed_code prog t.code ∧
    mem_config t.memory t.memaddrs t.be t.base_addr ∧
    mem_read_ffi_results (:α) t.ffi.ffi_state 1 ∧
    t.ffi =
    build_ffi (:'a) t.be (MAP explode (out_signals prog))
              t.ffi.ffi_state t.ffi.io_events ∧
    init_ffi t.ffi.ffi_state ∧
    input_time_rel t.ffi.ffi_state ∧
    time_seq t.ffi.ffi_state (dimword (:α)) ∧
    FST (t.ffi.ffi_state 0) < dimword (:α) − 1 ∧
    t.ffi.io_events = [] ∧
    good_dimindex (:'a) ∧
    ~MEM "get_time_input" (MAP explode (out_signals prog))
End

Definition systime_at_def:
  systime_at (t:('a,time_input) panSem$state) =
    FST (t.ffi.ffi_state 0)
End

Theorem length_get_bytes:
  ∀w be.
    LENGTH (get_bytes be (w:'a word)) = dimindex (:α) DIV 8
Proof
  rw [] >>
  fs [get_bytes_def]
QED

Theorem word_of_bytes_get_byte_eq_word_32:
  ∀x be.
    dimindex (:α) = 32 ⇒
    word_of_bytes
    be 0w
    [get_byte 0w x be; get_byte 1w x be; get_byte 2w x be;
     get_byte 3w x be] = (x:'a word)
Proof
  rw [] >>
  gs [word_of_bytes_def] >>
  cases_on ‘be’ >> gs [] >> (
  gvs [fcpTheory.CART_EQ] >>
  rw [] >>
  gs [set_byte_def, get_byte_def] >>
  gs [byte_index_def, word_slice_alt_def] >>
  gs [fcpTheory.FCP_BETA, word_or_def, dimword_def] >>
  gs [word_lsl_def, word_lsr_def, fcpTheory.FCP_BETA, w2w] >>
  srw_tac [CONJ_ss]
          [word_lsl_def, word_lsr_def, fcpTheory.FCP_BETA,
           w2w] >>
  gs [word_0] >>
  rw [] >> gs [] >>
  cases_on ‘i < 8’ >> gs [] >>
  cases_on ‘i < 16’ >> gs [] >>
  cases_on ‘i < 24’ >> gs [])
QED

Theorem word_of_bytes_get_byte_eq_word_64:
  ∀x be.
    dimindex (:α) = 64 ⇒
    word_of_bytes
    be 0w
    [get_byte 0w x be; get_byte 1w x be; get_byte 2w x be;
     get_byte 3w x be; get_byte 4w x be; get_byte 5w x be;
     get_byte 6w x be; get_byte 7w x be] = (x:'a word)
Proof
  rw [] >>
  gs [word_of_bytes_def] >>
  cases_on ‘be’ >> gs [] >> (
  gvs [fcpTheory.CART_EQ] >>
  rw [] >>
  gs [set_byte_def, get_byte_def] >>
  gs [byte_index_def] >>
  gs [word_slice_alt_def, fcpTheory.FCP_BETA, word_or_def,dimword_def,
      word_lsl_def, word_lsr_def, fcpTheory.FCP_BETA, w2w] >>
  srw_tac [CONJ_ss]
          [word_lsl_def, word_lsr_def, fcpTheory.FCP_BETA,
           w2w] >>
  gs [word_0] >>
  rw [] >> gs [] >>
  cases_on ‘i < 8’ >> gs [] >>
  cases_on ‘i < 16’ >> gs [] >>
  cases_on ‘i < 24’ >> gs [] >>
  cases_on ‘i < 32’ >> gs [] >>
  cases_on ‘i < 40’ >> gs [] >>
  cases_on ‘i < 48’ >> gs [] >>
  cases_on ‘i < 56’ >> gs [])
QED

Theorem words_of_bytes_get_byte:
  ∀xs x be.
    good_dimindex (:α) ∧
    xs = get_bytes be (x:'a word) ⇒
    words_of_bytes be xs = [x]
Proof
  Induct >>
  rw []
  >- gs [words_of_bytes_def, get_bytes_def, good_dimindex_def] >>
  pop_assum (assume_tac o GSYM) >>
  gs [] >>
  gs [words_of_bytes_def] >>
  gs [good_dimindex_def, bytes_in_word_def, dimword_def] >>
  gs [get_bytes_def] >>
  pop_assum (mp_tac o GSYM) >>
  pop_assum (mp_tac o GSYM) >>
  strip_tac >> strip_tac >>
  gs [words_of_bytes_def] >>
  gvs []
  >- (match_mp_tac word_of_bytes_get_byte_eq_word_32 >> gs []) >>
  match_mp_tac word_of_bytes_get_byte_eq_word_64 >> gs []
QED


Theorem words_of_bytes_get_bytes:
  ∀x y be.
    good_dimindex (:α) ⇒
    words_of_bytes be
      (get_bytes be (x:'a word) ++
       get_bytes be (y:'a word)) = [x;y]
Proof
  rw [] >>
  ‘0 < w2n (bytes_in_word:'a word)’ by
    gs [good_dimindex_def, bytes_in_word_def, dimword_def] >>
  drule words_of_bytes_append >>
  disch_then (qspecl_then
              [‘be’, ‘get_bytes be x’, ‘get_bytes be y’] mp_tac) >>
  impl_tac
  >- (
    gs [length_get_bytes] >>
    gs [good_dimindex_def, bytes_in_word_def, dimword_def]) >>
  strip_tac >>
  gs [] >>
  ‘words_of_bytes be (get_bytes be x) = [x]’ by (
    match_mp_tac words_of_bytes_get_byte >>
    gs []) >>
  ‘words_of_bytes be (get_bytes be y) = [y]’ by (
    match_mp_tac words_of_bytes_get_byte >>
    gs []) >>
  gs []
QED


Theorem eval_empty_const_eq_empty_vals:
  ∀s n.
    OPT_MMAP (λe. eval s e) (emptyConsts n) =
    SOME (emptyVals n)
Proof
  rw [] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  fs [emptyConsts_def, emptyVals_def] >>
  fs [LIST_REL_EL_EQN] >>
  rw [] >>
  ‘EL n' (REPLICATE n ((Const 0w):'a panLang$exp)) = Const 0w’ by (
    match_mp_tac EL_REPLICATE >>
    fs []) >>
  ‘EL n' (REPLICATE n (ValWord 0w)) = ValWord 0w’ by (
    match_mp_tac EL_REPLICATE >>
    fs []) >>
  fs [eval_def]
QED

Theorem opt_mmap_resetTermClocks_eq_resetClksVals:
  ∀t clkvals s clks tclks.
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    OPT_MMAP (λa. eval t a)
             (resetTermClocks «clks» clks tclks) =
    SOME (resetClksVals s.clocks clks tclks)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  conj_tac
  >- fs [resetTermClocks_def, resetClksVals_def] >>
  fs [LIST_REL_EL_EQN] >>
  conj_tac
  >- fs [resetTermClocks_def, resetClksVals_def] >>
  rw [] >>
  fs [resetTermClocks_def] >>
  TOP_CASE_TAC
  >- (
    ‘EL n (resetClksVals s.clocks clks tclks) = ValWord 0w’ by (
    fs [resetClksVals_def] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
    ‘EL n (MAP ff clks) = ff (EL n clks)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’] >>
    drule reset_clks_mem_flookup_zero >>
    disch_then (qspec_then ‘s.clocks’ mp_tac) >>
    fs []) >>
   fs [eval_def]) >>
  fs [equiv_val_def] >> rveq >> fs [] >>
  fs [EVERY_MEM] >>
  last_x_assum (qspec_then ‘EL n clks’ mp_tac) >>
  impl_tac
  >- (match_mp_tac EL_MEM >> fs []) >>
  strip_tac >>
  fs [FDOM_FLOOKUP] >>
  ‘EL n (resetClksVals s.clocks clks tclks) = ValWord (n2w v)’ by (
    fs [resetClksVals_def] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
    ‘EL n (MAP ff clks) = ff (EL n clks)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’] >>
    drule reset_clks_not_mem_flookup_same >>
    fs []) >>
  fs [] >>
  fs [eval_def] >>
  qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
  ‘EL n (MAP ff clks) = ff (EL n clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘ff’]
QED


Theorem maxClksSize_reset_clks_eq:
  ∀s clks (clkvals:α v list) tclks.
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    equiv_val s.clocks clks clkvals ∧
    maxClksSize clkvals  ⇒
    maxClksSize ((resetClksVals s.clocks clks tclks):α v list)
Proof
  rw [] >>
  fs [resetClksVals_def] >>
  fs [equiv_val_def] >> rveq >> fs [] >>
  fs [maxClksSize_def] >>
  fs [MAP_MAP_o] >>
  fs [SUM_MAP_FOLDL] >>
  qmatch_asmsub_abbrev_tac ‘FOLDL ff _ _’ >>
  qmatch_goalsub_abbrev_tac ‘FOLDL gg _ _’ >>
  ‘FOLDL ff 0 clks = FOLDL gg 0 clks ’ by (
    match_mp_tac FOLDL_CONG >>
    fs [Abbr ‘ff’, Abbr ‘gg’] >> rw [shape_of_def]) >>
  fs []
QED


Theorem calculate_wait_times_eq:
  ∀t vname clkvals s clks wt.
    FLOOKUP t.locals vname = SOME (Struct clkvals) ∧
    EVERY (λck. ck IN FDOM s.clocks) clks ∧
    equiv_val s.clocks clks clkvals ∧
    EVERY (λck. MEM ck clks) (MAP SND wt) ∧
    EVERY (λ(t,c). ∃v. FLOOKUP s.clocks c = SOME v ∧ v ≤ t) wt ⇒
    OPT_MMAP (λe. eval t e)
        (waitTimes (MAP FST wt)
         (MAP (λn. Field n (Var vname)) (indicesOf clks (MAP SND wt)))) =
    SOME (MAP (ValWord ∘ n2w ∘ THE ∘ evalDiff s) wt)
Proof
  rw [] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  rw [waitTimes_def, indicesOf_def, LIST_REL_EL_EQN] >>
  ‘SND (EL n wt) ∈ FDOM s.clocks’ by (
    fs [EVERY_MEM] >>
    first_x_assum (qspec_then ‘SND (EL n wt)’ mp_tac) >>
    impl_tac
    >- (
      drule EL_MEM >>
      fs [MEM_MAP] >>
      metis_tac []) >>
    strip_tac >>
    last_x_assum drule >>
    fs []) >>
  qmatch_goalsub_abbrev_tac ‘MAP2 ff xs ys’ >>
  ‘EL n (MAP2 ff xs ys) =
   ff (EL n xs) (EL n ys)’ by (
    match_mp_tac EL_MAP2 >>
    fs [Abbr ‘xs’, Abbr ‘ys’]) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘xs’] >>
  ‘EL n (MAP FST wt) = FST (EL n wt)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘ys’] >>
  fs [MAP_MAP_o] >>
  qmatch_goalsub_abbrev_tac ‘EL n (MAP gg _)’ >>
  ‘EL n (MAP gg wt) = gg (EL n wt)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac ‘MAP hh _’ >>
  ‘EL n (MAP hh wt) = hh (EL n wt)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘gg’, Abbr ‘ff’, Abbr ‘hh’] >>
  cases_on ‘EL n wt’ >> fs [] >>
  fs [evalDiff_def, evalExpr_def, EVERY_EL] >>
  fs [FDOM_FLOOKUP] >>
  fs [minusT_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  fs [eval_def] >>
  ‘findi r clks < LENGTH clkvals’ by (
    fs [equiv_val_def] >>
    match_mp_tac MEM_findi >>
    res_tac >> fs [] >>
    rfs [] >>
    ‘EL n (MAP SND wt) = SND (EL n wt)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    rfs [] >> rveq >> fs []) >>
  fs [] >>
  rfs [equiv_val_def] >>
  qmatch_goalsub_abbrev_tac ‘EL m (MAP ff _)’ >>
  ‘EL m (MAP ff clks) = ff (EL m clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘ff’, Abbr ‘m’] >>
  pop_assum kall_tac >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  ‘EL (findi r clks) clks = r’ by (
    match_mp_tac EL_findi >>
    res_tac >> fs [] >>
    rfs [] >>
    ‘EL n (MAP SND wt) = SND (EL n wt)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    rfs [] >> rveq >> fs []) >>
  fs [wordLangTheory.word_op_def] >>
  first_x_assum drule >>
  fs [] >>
  strip_tac >>
  ‘n2w (q − v):'a word = n2w q − n2w v’ suffices_by fs [] >>
  match_mp_tac n2w_sub >> rveq >> fs [] >> rveq >> rfs [] >>
  first_x_assum drule >>
  fs []
QED


Theorem eval_term_clkvals_equiv_reset_clkvals:
  ∀s io io' cnds tclks dest wt s' clks.
    evalTerm s io
             (Tm io' cnds tclks dest wt) s' ⇒
    equiv_val s'.clocks clks (resetClksVals s.clocks clks tclks)
Proof
  rw [] >>
  fs [evalTerm_cases] >>
  rveq >> fs [] >>
  fs [equiv_val_def] >>
  fs [resetClksVals_def]
QED


Theorem evaluate_minop_eq:
  ∀es s vname n ns res t.
    FLOOKUP s.locals vname = SOME (ValWord (n2w n)) ∧
    (∀n. n < LENGTH es ⇒ ~MEM vname (var_exp (EL n es))) ∧
    MAP (eval s) es = MAP (SOME ∘ ValWord ∘ (n2w:num -> α word)) ns ∧
    n < dimword (:α) ∧
    EVERY (λn. n < dimword (:α)) ns ∧
    evaluate (minOp vname es,s) = (res,t) ⇒
    res = NONE ∧
    t = s with locals:= s.locals |+
                         (vname,
                          ValWord (minOption (n2w n) (list_min_option ns)))
Proof
  Induct >>
  rpt gen_tac >>
  strip_tac >> fs []
  >- (
    fs [minOp_def, evaluate_def] >> rveq >>
    fs [minOption_def, list_min_option_def] >>
    cases_on ‘s’ >>
    fs [state_fn_updates] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac FUPDATE_ELIM >>
    fs [FLOOKUP_DEF]) >>
  cases_on ‘ns’ >> fs [] >>
  fs [minOp_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  fs [eval_def] >>
  rfs [] >>
  fs [asmTheory.word_cmp_def] >>
  cases_on ‘(n2w h'):'a word <₊ n2w n’ >>
  fs []
  >- (
    fs [evaluate_def] >>
    rfs [] >>
    fs [is_valid_value_def] >>
    rfs [] >>
    fs [panSemTheory.shape_of_def] >>
    rveq >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (_, stNew)’ >>
    last_x_assum
    (qspecl_then
     [‘stNew’, ‘vname’, ‘h'’, ‘t'’, ‘res’, ‘t’] mp_tac) >>
    fs [Abbr ‘stNew’] >>
    fs [FLOOKUP_UPDATE] >>
    impl_tac
    >- (
      reverse conj_tac
      >- (
        fs [MAP_EQ_EVERY2] >>
        fs [LIST_REL_EL_EQN] >>
        rw [] >>
        match_mp_tac update_locals_not_vars_eval_eq >>
        last_x_assum (qspec_then ‘SUC n'’ mp_tac) >>
        fs []) >>
      rw [] >> fs [] >>
      last_x_assum (qspec_then ‘SUC n'’ mp_tac) >>
      fs []) >>
    strip_tac >>
    fs [list_min_option_def] >>
    cases_on ‘list_min_option t'’ >> fs []
    >- (
    fs [minOption_def] >>
    ‘~(n2w n <₊ n2w h')’ by (
      fs [WORD_NOT_LOWER] >>
      gs [WORD_LOWER_OR_EQ]) >>
    fs []) >>
    drule list_min_option_some_mem >>
    strip_tac >>
    fs [EVERY_MEM] >>
    first_x_assum (qspec_then ‘x’ mp_tac) >>
    fs [] >>
    strip_tac >>
    cases_on ‘h' < x’ >> fs []
    >- (
    fs [minOption_def] >>
     ‘~(n2w n <₊ n2w h')’ by (
      fs [WORD_NOT_LOWER] >>
      gs [WORD_LOWER_OR_EQ]) >>
     fs [] >>
    qsuff_tac ‘(n2w h'):'a word <₊ n2w x’ >- fs [] >>
    fs [word_lo_n2w]) >>
    fs [minOption_def] >>
    ‘~((n2w h'):'a word <₊ n2w x)’ by (
      fs [WORD_NOT_LOWER, NOT_LESS, word_ls_n2w]) >>
    fs [] >>
    ‘~((n2w n):'a word <₊ n2w x)’ by (
      fs [WORD_NOT_LOWER] >>
      fs [NOT_LESS] >>
      ‘h' < n’ by gs [word_lo_n2w] >>
      ‘x < n’ by gs [] >>
      gs [word_ls_n2w]) >>
    fs []) >>
  fs [evaluate_def] >>
  rfs [] >> rveq >>
  last_x_assum
  (qspecl_then
   [‘s’, ‘vname’, ‘n’, ‘t'’, ‘res’, ‘t’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
    rw [] >>
    last_x_assum (qspec_then ‘SUC n'’ mp_tac) >>
    fs []) >>
  strip_tac >>
  fs [] >>
  fs [list_min_option_def] >>
  cases_on ‘list_min_option t'’ >> fs []
  >- (
    fs [minOption_def] >>
    fs [WORD_NOT_LOWER] >>
    gs [WORD_LOWER_OR_EQ]) >>
  fs [minOption_def] >>
  every_case_tac >> fs [WORD_NOT_LOWER]
  >- (
    qsuff_tac ‘h' = n’ >- fs [] >>
    qsuff_tac ‘h' ≤ n ∧ n ≤ h'’ >- fs [] >>
    gs [word_ls_n2w]) >> (
  drule list_min_option_some_mem >>
  strip_tac >>
  fs [EVERY_MEM] >>
  first_x_assum (qspec_then ‘x’ mp_tac) >>
  impl_tac >- fs [] >>
  strip_tac >>
  gs [word_ls_n2w])
QED


Theorem evaluate_min_exp_eq:
  ∀es s vname v ns res t.
    FLOOKUP s.locals vname = SOME (ValWord v) ∧
    (∀n. n < LENGTH es ⇒ ~MEM vname (var_exp (EL n es))) ∧
    MAP (eval s) es = MAP (SOME ∘ ValWord ∘ (n2w:num -> α word)) ns ∧
    EVERY (λn. n < dimword (:α)) ns ∧
    evaluate (minExp vname es,s) = (res,t) ⇒
    res = NONE ∧
    (es = [] ⇒ t = s) ∧
    (es ≠ [] ⇒
     t = s with locals :=
         s.locals |+
          (vname, ValWord ((n2w:num -> α word) (THE (list_min_option ns)))))
Proof
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘es’ >> fs []
  >- (
    fs [minExp_def] >>
    fs [evaluate_def]) >>
  cases_on ‘ns’ >> fs [] >>
  fs [minExp_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  rfs [] >>
  fs [is_valid_value_def] >>
  rfs [] >>
  fs [panSemTheory.shape_of_def] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (_,stInit)’ >>
  ‘FLOOKUP stInit.locals vname = SOME (ValWord (n2w h'))’ by (
    fs [Abbr ‘stInit’] >>
    fs [FLOOKUP_UPDATE]) >>
  last_x_assum mp_tac >>
  drule evaluate_minop_eq >>
  disch_then (qspecl_then [‘t'’, ‘t''’, ‘res’, ‘t’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
    conj_tac
    >- (
      rw [] >>
      last_x_assum (qspec_then ‘SUC n’ mp_tac) >>
      fs []) >>
    fs [Abbr ‘stInit’] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    match_mp_tac update_locals_not_vars_eval_eq >>
    last_x_assum (qspec_then ‘SUC n’ mp_tac) >>
    fs []) >>
  rpt strip_tac >> fs [] >>
  fs [list_min_option_def] >>
  cases_on ‘list_min_option t''’ >> fs [] >>
  fs [Abbr ‘stInit’, minOption_def] >>
  drule list_min_option_some_mem >>
  strip_tac >>
  fs [EVERY_MEM] >>
  first_x_assum (qspec_then ‘x’ mp_tac) >>
  fs [] >>
  strip_tac >>
  every_case_tac
  >- (
    fs [NOT_LESS] >>
    qsuff_tac ‘h' < x’ >- fs [] >>
    gs [word_lo_n2w]) >>
  fs [WORD_NOT_LOWER] >>
  gs [word_ls_n2w]
QED


Theorem every_conj_spec:
  ∀fm (m:num) xs w.
    EVERY
    (λck. ∃n. FLOOKUP fm ck = SOME n ∧
              n < m) xs ⇒
    EVERY (λck. ck IN FDOM fm) xs
Proof
  rw [] >>
  fs [EVERY_MEM] >>
  rw [] >>
  last_x_assum drule >>
  strip_tac >> fs [FDOM_FLOOKUP]
QED


Theorem shape_of_resetClksVals_eq:
  ∀fm (clks:mlstring list) (tclks:mlstring list) (clkvals:'a v list).
    EVERY (λv. ∃w. v = ValWord w) clkvals /\
    LENGTH clks = LENGTH clkvals ⇒
    MAP ((λa. size_of_shape a) ∘ (λa. shape_of a))
        ((resetClksVals fm clks tclks):'a v list) =
    MAP ((λa. size_of_shape a) ∘ (λa. shape_of a)) clkvals
Proof
  rw [] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  fs [resetClksVals_def] >>
  rw [] >> fs [] >>
  qmatch_goalsub_abbrev_tac ‘MAP f _’ >>
  ‘EL n (MAP f clks) = f (EL n clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘f’] >>
  pop_assum kall_tac >>
  fs [EVERY_MEM] >>
  drule EL_MEM >>
  strip_tac >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  fs [panSemTheory.shape_of_def]
QED

Theorem comp_input_term_correct:
  ∀s n cnds tclks dest wt s' t (clkvals:'a v list) clks (m:num).
    evalTerm s (SOME n)
             (Tm (Input n) cnds tclks dest wt) s' ∧
    m = dimword (:α) - 1 ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks m ∧
    time_range wt m ∧
    equiv_val s.clocks clks clkvals ∧
    valid_clks clks tclks wt ∧
    num_to_str dest IN FDOM t.code ⇒
      evaluate (compTerm clks (Tm (Input n) cnds tclks dest wt), t) =
      (SOME (Return (retVal s clks tclks wt dest)),
       t with locals :=
       restore_from t FEMPTY [«waitTimes»; «newClks»; «wakeUpAt»; «waitSet»])
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [clock_bound_def, time_range_def] >>
  drule every_conj_spec >>
  strip_tac >>
  drule eval_term_clkvals_equiv_reset_clkvals >>
  disch_then (qspec_then ‘clks’ assume_tac) >>
  fs [evalTerm_cases] >>
  rveq >> fs [] >>
  fs [compTerm_def] >>
  cases_on ‘wt’
  >- ( (* wait set is disabled *)
   fs [panLangTheory.decs_def] >>
   fs [evaluate_def] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   rfs [] >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stInit a) _’ >>
   ‘OPT_MMAP (λa. eval stInit a)
      (resetTermClocks «clks» clks tclks) =
    SOME (resetClksVals s.clocks clks tclks)’ by (
     match_mp_tac opt_mmap_resetTermClocks_eq_resetClksVals >>
     qexists_tac ‘clkvals’ >> rfs [] >>
     fs [Abbr ‘stInit’] >>
     rfs [FLOOKUP_UPDATE]) >>
   fs [] >>
   pop_assum kall_tac >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [emptyConsts_def] >>
   fs [OPT_MMAP_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [panLangTheory.nested_seq_def] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [eval_def] >>
   fs [indicesOf_def, waitTimes_def, minExp_def] >>
   pop_assum mp_tac >>
   rewrite_tac [OPT_MMAP_def] >>
   strip_tac >>
   fs [is_valid_value_def] >>
   fs [FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stReset a) _’ >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >>
   fs [Abbr ‘stReset’, FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
   rfs [] >>
   fs [panSemTheory.shape_of_def, panLangTheory.size_of_shape_def] >>
   fs [GSYM FDOM_FLOOKUP] >>
   drule maxClksSize_reset_clks_eq >>
   disch_then (qspecl_then [‘clkvals’, ‘tclks’] mp_tac) >>
   fs [] >> strip_tac >>
   fs [maxClksSize_def, MAP_MAP_o, ETA_AX] >>
   pop_assum kall_tac >>
   rveq >> fs [] >> rfs [] >> rveq >> fs [] >>
   fs [empty_locals_def, retVal_def] >>
   fs [restore_from_def]) >>
  (* some maintenance to replace h::t' to wt *)
  qmatch_goalsub_abbrev_tac ‘emptyConsts (LENGTH wt)’ >>
  ‘(case wt of [] => Const 1w | v2::v3 => Const 0w) =
   (Const 0w): 'a panLang$exp’ by fs [Abbr ‘wt’] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [panLangTheory.decs_def] >>
  fs [evaluate_def] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  rfs [] >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stInit a) _’ >>
  ‘OPT_MMAP (λa. eval stInit a)
   (resetTermClocks «clks» clks tclks) =
   SOME (resetClksVals s.clocks clks tclks)’ by (
    match_mp_tac opt_mmap_resetTermClocks_eq_resetClksVals >>
    qexists_tac ‘clkvals’ >> rfs [] >>
    fs [Abbr ‘stInit’] >>
    rfs [FLOOKUP_UPDATE]) >>
  fs [] >>
  pop_assum kall_tac >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [eval_empty_const_eq_empty_vals] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [panLangTheory.nested_seq_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  qmatch_asmsub_abbrev_tac ‘eval stReset _’ >>
  fs [eval_def] >>
  (* waitimes eq eval diffs *)
  ‘OPT_MMAP (λa. eval stReset a)
   (waitTimes (MAP FST wt)
    (MAP (λn. Field n (Var «newClks» ))
     (indicesOf clks (MAP SND wt)))) =
   SOME (MAP ((λw. ValWord w) ∘ n2w ∘ THE ∘ evalDiff
              (s with clocks := resetClocks s.clocks tclks)) wt)’ by (
    match_mp_tac calculate_wait_times_eq >>
    qexists_tac ‘resetClksVals s.clocks clks tclks’ >>
    rfs [Abbr ‘stReset’] >>
    rewrite_tac [FLOOKUP_UPDATE] >>
    fs [] >>
    fs [equiv_val_def] >>
    last_x_assum assume_tac >>
    drule fdom_reset_clks_eq_clks >>
    strip_tac >>
    rfs [valid_clks_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    last_x_assum (qspec_then ‘e’ mp_tac) >>
    fs [] >>
    cases_on ‘e’ >> fs [] >>
    strip_tac >>
    fs [] >>
    match_mp_tac flookup_reset_clks_leq >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘is_valid_value tt _ wtval’ >>
  ‘is_valid_value tt «waitTimes» wtval’ by (
    fs [Abbr ‘tt’, Abbr ‘wtval’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [panSemTheory.shape_of_def] >>
    fs [emptyVals_def, emptyConsts_def] >>
    fs [MAP_MAP_o, GSYM MAP_K_REPLICATE, MAP_EQ_f] >>
    rw [] >>
    fs [shape_of_def]) >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (minExp _ es, stWait)’ >>
  ‘FLOOKUP stWait.locals «wakeUpAt» = SOME (ValWord 0w)’ by
    fs [Abbr ‘stWait’, FLOOKUP_UPDATE] >>
  drule evaluate_min_exp_eq >>
  disch_then (
    qspecl_then [
        ‘es’,
        ‘MAP (THE o evalDiff (s with clocks := resetClocks s.clocks tclks)) wt’,
        ‘res''’, ‘s1'’] mp_tac) >>
  impl_tac
  >- (
   rfs [] >>
   conj_tac
   >- (
    rw [] >>
    fs [Abbr ‘es’] >>
    fs [panLangTheory.var_exp_def]) >>
   conj_tac
   >- (
    fs [Abbr ‘stWait’, Abbr ‘es’] >>
    fs [Abbr ‘wtval’] >>
    fs [MAP_MAP_o] >>
    fs [MAPi_enumerate_MAP] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    fs [LENGTH_enumerate] >>
    rw [] >>
    pairarg_tac >> fs [] >>
    ‘EL n (enumerate 0 wt) = (n+0,EL n wt)’ by (
      match_mp_tac EL_enumerate >>
      fs []) >>
    fs [] >>
    pop_assum kall_tac >>
    fs [eval_def] >>
    fs [FLOOKUP_UPDATE] >>
    rveq >> rfs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
    ‘EL i (MAP ff wt) = ff (EL i wt)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’]) >>
   fs [EVERY_MAP, EVERY_MEM] >>
   gen_tac >>
   strip_tac >>
   cases_on ‘x’ >>
   fs [evalDiff_def, evalExpr_def] >>
   cases_on ‘MEM r tclks’
   >- (
    drule reset_clks_mem_flookup_zero >>
    disch_then (qspec_then ‘s.clocks’ assume_tac) >>
    fs [] >>
    fs [minusT_def] >>
    first_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
    fs []) >>
   rfs [valid_clks_def] >>
   rfs [EVERY_MEM] >>
   ‘MEM r clks’ by (
     ‘MEM r (MAP SND wt)’ by (
       fs [MEM_MAP] >>
       qexists_tac ‘(q,r)’ >> fs []) >>
     res_tac >> gs []) >>
   res_tac >> rfs [] >>
   drule reset_clks_not_mem_flookup_same >>
   disch_then (qspec_then ‘tclks’ mp_tac) >>
   rfs [] >>
   strip_tac >>
   fs [minusT_def] >>
   last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
   fs [] >>
   strip_tac >>
   last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
   gs []) >>
  strip_tac >> fs [] >>
  ‘es ≠ []’ by fs [Abbr ‘wt’, Abbr ‘es’] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  unabbrev_all_tac >> fs [] >> rveq >> rfs [] >>
  fs [OPT_MMAP_def, eval_def, FLOOKUP_UPDATE] >>
  rfs [FDOM_FLOOKUP] >>
  rfs [] >>
  fs [panLangTheory.size_of_shape_def, panSemTheory.shape_of_def] >>
  fs [MAP_MAP_o] >>
  qmatch_asmsub_abbrev_tac ‘SUM ss’ >>
  ‘ss =
   MAP ((λa. size_of_shape a) ∘ (λa. shape_of a)) clkvals’ by (
    fs [Abbr ‘ss’] >>
    match_mp_tac shape_of_resetClksVals_eq >>
    rfs [equiv_val_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    fs [MEM_MAP]) >>
  rfs [maxClksSize_def] >>
  qmatch_asmsub_abbrev_tac ‘ss = tt’ >>
  ‘SUM ss + 3 ≤ 32’ by fs [ETA_AX] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [empty_locals_def] >>
  rveq >> fs [] >> rveq >> rfs [] >>
  fs [restore_from_def] >>
  fs [retVal_def] >>
  fs [calculate_wtime_def]
QED


Theorem ffi_eval_state_thm:
  !ffi_name s (res:'a result option) t nbytes.
    evaluate
    (ExtCall ffi_name «ptr1» «len1» «ptr2» «len2»,s) = (res,t)∧
    well_behaved_ffi ffi_name s
                     (w2n (ffiBufferSize:'a word)) (dimword (:α))  /\
    FLOOKUP s.locals «ptr1» = SOME (ValWord 0w) ∧
    FLOOKUP s.locals «len1» = SOME (ValWord 0w) ∧
    FLOOKUP s.locals «ptr2» = SOME (ValWord s.base_addr) ∧
    FLOOKUP s.locals «len2» = SOME (ValWord ffiBufferSize) ==>
    res = NONE ∧
    ∃bytes.
      t = ffi_return_state s ffi_name bytes
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [well_behaved_ffi_def] >>
  gs [evaluate_def] >>
  gs [read_bytearray_def] >>
  dxrule LESS_MOD >>
  strip_tac >> rfs [] >>
  pop_assum kall_tac >>
  rfs [ffiTheory.call_FFI_def] >>
  rveq >> fs [] >>
  gs [ffi_return_state_def] >>
  rveq >> gs[] >>
  qexists_tac ‘bytes’ >>
  gs [state_component_equality,
      ffiTheory.ffi_state_component_equality]
QED

Theorem comp_output_term_correct:
  ∀s out cnds tclks dest wt s' t (clkvals:'a v list) clks m.
    evalTerm s NONE
             (Tm (Output out) cnds tclks dest wt) s' ∧
    m = dimword (:'a) - 1 ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks m ∧
    time_range wt m ∧
    equiv_val s.clocks clks clkvals ∧
    valid_clks clks tclks wt ∧
    num_to_str dest IN FDOM t.code ∧
    well_behaved_ffi (num_to_str out) t
                     (w2n (ffiBufferSize:'a word)) (dimword (:α)) ⇒
    ∃bytes.
      evaluate (compTerm clks (Tm (Output out) cnds tclks dest wt), t) =
      (SOME (Return (retVal s clks tclks wt dest)),
       t with
         <|locals :=
           restore_from t FEMPTY [«len2»; «ptr2»; «len1»; «ptr1»;
                                  «waitTimes»; «newClks»; «wakeUpAt»; «waitSet»];
           memory := write_bytearray t.base_addr bytes
                                     t.memory t.memaddrs t.be;
           ffi := nffi_state t out bytes|>)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [clock_bound_def, time_range_def] >>
  drule every_conj_spec >>
  strip_tac >>
  drule eval_term_clkvals_equiv_reset_clkvals >>
  disch_then (qspec_then ‘clks’ assume_tac) >>
  fs [evalTerm_cases] >>
  rveq >> fs [] >>
  fs [compTerm_def] >>
  cases_on ‘wt’
  >- ( (* wait set is disabled *)
   fs [panLangTheory.decs_def] >>
   fs [evaluate_def, eval_def] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   rfs [] >> fs [] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stInit a) _’ >>
   ‘OPT_MMAP (λa. eval stInit a)
      (resetTermClocks «clks» clks tclks) =
    SOME (resetClksVals s.clocks clks tclks)’ by (
     match_mp_tac opt_mmap_resetTermClocks_eq_resetClksVals >>
     qexists_tac ‘clkvals’ >> rfs [] >>
     fs [Abbr ‘stInit’] >>
     rfs [FLOOKUP_UPDATE]) >>
   fs [] >>
   pop_assum kall_tac >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [emptyConsts_def] >>
   fs [OPT_MMAP_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [panLangTheory.nested_seq_def] >>
   fs [Once evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >>
   fs [eval_def] >>
   fs [indicesOf_def, waitTimes_def, minExp_def] >>
   pop_assum mp_tac >>
   rewrite_tac [OPT_MMAP_def] >>
   strip_tac >>
   fs [is_valid_value_def] >>
   fs [FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   fs [eval_def] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   fs [Once evaluate_def] >> rveq >> fs [] >>
   pairarg_tac >> fs [] >> rveq >> rfs [] >>
   drule ffi_eval_state_thm >>
   disch_then (qspec_then ‘nbytes’ mp_tac) >>
   impl_tac
   >- (
    fs [FLOOKUP_UPDATE] >>
    fs [well_behaved_ffi_def]) >>
   strip_tac >> fs [] >> rveq >> fs [] >>
   fs [ffi_return_state_def] >>
   fs [evaluate_def] >>
   fs [eval_def] >>
   qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stReset a) _’ >>
   fs [OPT_MMAP_def] >>
   fs [eval_def] >>
   fs [Abbr ‘stReset’, FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
   rfs [] >>
   fs [panSemTheory.shape_of_def, panLangTheory.size_of_shape_def] >>
   fs [GSYM FDOM_FLOOKUP] >>
   drule maxClksSize_reset_clks_eq >>
   disch_then (qspecl_then [‘clkvals’, ‘tclks’] mp_tac) >>
   fs [] >> strip_tac >>
   fs [maxClksSize_def, MAP_MAP_o, ETA_AX] >>
   pop_assum kall_tac >>
   rveq >> fs [] >> rfs [] >> rveq >> fs [] >>
   fs [empty_locals_def, retVal_def] >>
   fs [nffi_state_def, restore_from_def] >>
   qexists_tac ‘bytes’ >>
   gs []) >>
  (* some maintenance to replace h::t' to wt *)
  qmatch_goalsub_abbrev_tac ‘emptyConsts (LENGTH wt)’ >>
  ‘(case wt of [] => Const 1w | v2::v3 => Const 0w) =
   (Const 0w): 'a panLang$exp’ by fs [Abbr ‘wt’] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [panLangTheory.decs_def] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  rfs [] >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stInit a) _’ >>
  ‘OPT_MMAP (λa. eval stInit a)
   (resetTermClocks «clks» clks tclks) =
   SOME (resetClksVals s.clocks clks tclks)’ by (
    match_mp_tac opt_mmap_resetTermClocks_eq_resetClksVals >>
    qexists_tac ‘clkvals’ >> rfs [] >>
    fs [Abbr ‘stInit’] >>
    rfs [FLOOKUP_UPDATE]) >>
  fs [] >>
  pop_assum kall_tac >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  fs [eval_empty_const_eq_empty_vals] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [panLangTheory.nested_seq_def] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘eval stReset _’ >>
  fs [eval_def] >>
  (* waitimes eq eval diffs *)
  ‘OPT_MMAP (λa. eval stReset a)
   (waitTimes (MAP FST wt)
    (MAP (λn. Field n (Var «newClks» ))
     (indicesOf clks (MAP SND wt)))) =
   SOME (MAP ((λw. ValWord w) ∘ n2w ∘ THE ∘ evalDiff
              (s with clocks := resetClocks s.clocks tclks)) wt)’ by (
    match_mp_tac calculate_wait_times_eq >>
    qexists_tac ‘resetClksVals s.clocks clks tclks’ >>
    rfs [Abbr ‘stReset’] >>
    rewrite_tac [FLOOKUP_UPDATE] >>
    fs [] >>
    fs [equiv_val_def] >>
    last_x_assum assume_tac >>
    drule fdom_reset_clks_eq_clks >>
    strip_tac >>
    rfs [valid_clks_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    last_x_assum (qspec_then ‘e’ mp_tac) >>
    fs [] >>
    cases_on ‘e’ >> fs [] >>
    strip_tac >>
    fs [] >>
    match_mp_tac flookup_reset_clks_leq >>
    fs []) >>
  fs [] >>
  pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘is_valid_value tt _ wtval’ >>
  ‘is_valid_value tt «waitTimes» wtval’ by (
    fs [Abbr ‘tt’, Abbr ‘wtval’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [panSemTheory.shape_of_def] >>
    fs [emptyVals_def, emptyConsts_def] >>
    fs [MAP_MAP_o, GSYM MAP_K_REPLICATE, MAP_EQ_f] >>
    rw [] >>
    fs [shape_of_def]) >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (minExp _ es, stWait)’ >>
  ‘FLOOKUP stWait.locals «wakeUpAt» = SOME (ValWord 0w)’ by
    fs [Abbr ‘stWait’, FLOOKUP_UPDATE] >>
  drule evaluate_min_exp_eq >>
  disch_then (
    qspecl_then [
        ‘es’,
        ‘MAP (THE ∘ evalDiff (s with clocks := resetClocks s.clocks tclks)) wt’,
        ‘res''’, ‘s1'’] mp_tac) >>
  impl_tac
  >- (
   rfs [] >>
   conj_tac
   >- (
    rw [] >>
    fs [Abbr ‘es’] >>
    fs [panLangTheory.var_exp_def]) >>
   conj_tac
   >- (
    fs [Abbr ‘stWait’, Abbr ‘es’] >>
    fs [Abbr ‘wtval’] >>
    fs [MAP_MAP_o] >>
    fs [MAPi_enumerate_MAP] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    fs [LENGTH_enumerate] >>
    rw [] >>
    pairarg_tac >> fs [] >>
    ‘EL n (enumerate 0 wt) = (n+0,EL n wt)’ by (
      match_mp_tac EL_enumerate >>
      fs []) >>
    fs [] >>
    pop_assum kall_tac >>
    fs [eval_def] >>
    fs [FLOOKUP_UPDATE] >>
    rveq >> rfs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
    ‘EL i (MAP ff wt) = ff (EL i wt)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’]) >>
   fs [EVERY_MAP, EVERY_MEM] >>
   gen_tac >>
   strip_tac >>
   cases_on ‘x’ >>
   fs [evalDiff_def, evalExpr_def] >>
   cases_on ‘MEM r tclks’
   >- (
    drule reset_clks_mem_flookup_zero >>
    disch_then (qspec_then ‘s.clocks’ assume_tac) >>
    fs [] >>
    fs [minusT_def] >>
    first_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
    fs []) >>
   rfs [valid_clks_def] >>
   rfs [EVERY_MEM] >>
   ‘MEM r clks’ by (
     ‘MEM r (MAP SND wt)’ by (
       fs [MEM_MAP] >>
       qexists_tac ‘(q,r)’ >> fs []) >>
     res_tac >> gs []) >>
   res_tac >> rfs [] >>
   drule reset_clks_not_mem_flookup_same >>
   disch_then (qspec_then ‘tclks’ mp_tac) >>
   rfs [] >>
   strip_tac >>
   fs [minusT_def] >>
   last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
   fs [] >>
   strip_tac  >>
   last_x_assum (qspec_then ‘(q,r)’ mp_tac) >>
   fs []) >>
  strip_tac >> fs [] >>
  ‘es ≠ []’ by fs [Abbr ‘wt’, Abbr ‘es’] >>
  fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  fs [eval_def] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  fs [Once evaluate_def] >> rveq >> fs [] >>
  pairarg_tac >> fs [] >> rveq >> rfs [] >>
  unabbrev_all_tac >> fs [] >> rveq >> rfs [] >>
  drule ffi_eval_state_thm >>
  disch_then (qspec_then ‘bytes’ mp_tac) >>
  impl_tac
  >- (
  fs [FLOOKUP_UPDATE] >>
  fs [well_behaved_ffi_def]) >>
  strip_tac >> fs [] >> rveq >> fs [] >>
  fs [ffi_return_state_def] >>
  fs [evaluate_def] >>
  fs [eval_def] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (λa. eval stReset a) _’ >>
  fs [OPT_MMAP_def] >>
  fs [eval_def] >>
  fs [Abbr ‘stReset’, FLOOKUP_UPDATE, FDOM_FLOOKUP] >>
  rfs [] >>
  fs [panLangTheory.size_of_shape_def, panSemTheory.shape_of_def] >>
  fs [MAP_MAP_o] >>
  qmatch_asmsub_abbrev_tac ‘SUM ss’ >>
  ‘ss =
   MAP ((λa. size_of_shape a) ∘ (λa. shape_of a)) clkvals’ by (
    fs [Abbr ‘ss’] >>
    match_mp_tac shape_of_resetClksVals_eq >>
    rfs [equiv_val_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    fs [MEM_MAP]) >>
  rfs [maxClksSize_def] >>
  qmatch_asmsub_abbrev_tac ‘ss = tt’ >>
  ‘SUM ss + 3 ≤ 32’ by fs [ETA_AX] >>
  fs [] >>
  pop_assum kall_tac >>
  fs [empty_locals_def] >>
  rveq >> fs [] >> rveq >> rfs [] >>
  fs [restore_from_def] >>
  fs [retVal_def] >>
  fs [calculate_wtime_def] >>
  fs [nffi_state_def] >>
  qexists_tac ‘bytes’ >>
  gs []
QED


Theorem comp_term_correct:
  ∀s io ioAct cnds tclks dest wt s' t (clkvals:'a v list) clks m.
    evalTerm s io
             (Tm ioAct cnds tclks dest wt) s' ∧
    m = dimword (:'a) - 1 ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks m ∧
    time_range wt m ∧
    equiv_val s.clocks clks clkvals ∧
    valid_clks clks tclks wt ∧
    num_to_str dest IN FDOM t.code ⇒
    case (io,ioAct) of
     | (SOME _,Input n) =>
         evaluate (compTerm clks (Tm (Input n) cnds tclks dest wt), t) =
         (SOME (Return (retVal s clks tclks wt dest)),
          (* we can throw away the locals *)
          t with locals :=
          restore_from t FEMPTY [«waitTimes»; «newClks»; «wakeUpAt»; «waitSet»])
     | (NONE, Output out) =>
         (well_behaved_ffi (num_to_str out) t
                           (w2n (ffiBufferSize:'a word)) (dimword (:α)) ⇒
          ∃bytes.
            evaluate (compTerm clks (Tm (Output out) cnds tclks dest wt), t) =
            (SOME (Return (retVal s clks tclks wt dest)),
             t with
               <|locals :=
                 restore_from t FEMPTY [«len2»; «ptr2»; «len1»; «ptr1»;
                                        «waitTimes»; «newClks»; «wakeUpAt»; «waitSet»];
                 memory := write_bytearray t.base_addr bytes
                                           t.memory t.memaddrs t.be;
                 ffi := nffi_state t out bytes|>))
     | (_,_) => F
Proof
  rw [] >>
  cases_on ‘ioAct’ >>
  cases_on ‘io’ >>
  fs [] >>
  TRY (fs[evalTerm_cases] >> NO_TAC)
  >- (
    drule eval_term_inpput_ios_same >>
    strip_tac >> rveq >>
    match_mp_tac comp_input_term_correct >>
    gs [] >>
    metis_tac []) >>
  strip_tac >>
  drule comp_output_term_correct >>
  gs []
QED


Theorem comp_exp_correct:
  ∀s e n clks t:('a,'b)panSem$state clkvals.
    evalExpr s e = SOME n ∧
    EVERY (λck. MEM ck clks) (exprClks [] e) ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    eval t (compExp clks «clks» e) = SOME (ValWord (n2w n))
Proof
  ho_match_mp_tac evalExpr_ind >>
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘e’ >> fs []
  >- (
    fs [evalExpr_def] >>
    fs [compExp_def] >>
    fs [eval_def])
  >- (
    fs [evalExpr_def, timeLangTheory.exprClks_def] >>
    fs [compExp_def] >>
    fs [equiv_val_def] >> rveq >> gs [] >>
    fs [eval_def] >>
    ‘findi m clks < LENGTH clks’ by (
      match_mp_tac MEM_findi >>
      gs []) >>
    fs [] >>
    qmatch_goalsub_abbrev_tac ‘EL nn (MAP ff _)’ >>
    ‘EL nn (MAP ff clks) = ff (EL nn clks)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [Abbr ‘ff’, Abbr ‘nn’] >>
    pop_assum kall_tac >>
    ‘EL (findi m clks) clks = m’ by (
      match_mp_tac EL_findi >>
      gs []) >>
    fs []) >>
  qpat_x_assum ‘evalExpr _ _ = _’ mp_tac >>
  rewrite_tac [Once evalExpr_def] >>
  fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  strip_tac >>
  qpat_x_assum ‘EVERY _ (exprClks [] _)’ mp_tac >>
  once_rewrite_tac [timeLangTheory.exprClks_def] >>
  fs [] >>
  strip_tac >>
  ‘EVERY (λck. MEM ck clks) (exprClks [] e0) ∧
   EVERY (λck. MEM ck clks) (exprClks [] e')’ by (
    drule exprClks_accumulates >>
    fs [] >>
    strip_tac >>
    fs [EVERY_MEM] >>
    rw [] >>
    fs [] >>
    drule exprClks_sublist_accum >>
    fs []) >>
  fs [] >>
  last_x_assum drule >>
  last_x_assum drule >>
  fs [] >>
  disch_then (qspecl_then [‘t’, ‘clkvals’] assume_tac) >>
  disch_then (qspecl_then [‘t’, ‘clkvals’] assume_tac) >>
  gs [] >>
  rewrite_tac [compExp_def] >>
  fs [eval_def] >>
  gs [OPT_MMAP_def] >>
  fs [wordLangTheory.word_op_def] >>
  match_mp_tac EQ_SYM >>
  rewrite_tac [Once evalExpr_def] >>
  fs [minusT_def] >>
  rveq >> gs [] >>
  drule n2w_sub >>
  fs []
QED



Theorem comp_condition_true_correct:
  ∀s cnd m (t:('a,'b) panSem$state) clks clkvals.
    evalCond s cnd ∧
    m = dimword (:α) - 1 ∧
    EVERY (λe. case (evalExpr s e) of
               | SOME n => n < m
               | _ => F) (destCond cnd) ∧
    EVERY (λck. MEM ck clks) (condClks cnd) ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    eval t (compCondition clks «clks» cnd) = SOME (ValWord 1w)
Proof
  rw [] >>
  cases_on ‘cnd’ >>
  fs [evalCond_def, timeLangTheory.condClks_def,
      timeLangTheory.destCond_def, timeLangTheory.clksOfExprs_def] >>
  every_case_tac >> fs [] >>
  ‘x MOD dimword (:α) = x’ by (
    match_mp_tac LESS_MOD >>
    gs []) >>
  ‘x' MOD dimword (:α) = x'’ by (
    match_mp_tac LESS_MOD >>
    gs [])
  >- (
   dxrule comp_exp_correct >>
   disch_then
   (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
   impl_tac
   >- (
     fs [] >>
     drule exprClks_accumulates >>
     fs []) >>
   strip_tac >>
   dxrule comp_exp_correct >>
   disch_then
   (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
   impl_tac
   >- (
    fs [EVERY_MEM] >>
    rw [] >>
    fs [] >>
    drule exprClks_sublist_accum >>
    fs []) >>
   strip_tac >>
   fs [compCondition_def] >>
   fs [eval_def, OPT_MMAP_def] >>
   gs [] >>
   fs [asmTheory.word_cmp_def] >>
   gs [word_lo_n2w] >>
   gs [LESS_OR_EQ, wordLangTheory.word_op_def]) >>
  dxrule comp_exp_correct >>
  disch_then
  (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
  impl_tac
  >- (
  fs [] >>
  drule exprClks_accumulates >>
  fs []) >>
  strip_tac >>
  dxrule comp_exp_correct >>
  disch_then
  (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
  impl_tac
  >- (
  fs [EVERY_MEM] >>
  rw [] >>
  fs [] >>
  drule exprClks_sublist_accum >>
  fs []) >>
  strip_tac >>
  fs [compCondition_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  gs [] >>
  fs [asmTheory.word_cmp_def] >>
  gs [word_lo_n2w]
QED


Theorem map_comp_conditions_true_correct:
  ∀cnds s m (t:('a,'b) panSem$state) clks clkvals.
    EVERY (λcnd. evalCond s cnd) cnds ∧
    m = dimword (:α) - 1 ∧
    EVERY
    (λcnd.
      EVERY (λe. case (evalExpr s e) of
                 | SOME n => n < m
                 | _ => F) (destCond cnd)) cnds ∧
    EVERY
    (λcnd. EVERY (λck. MEM ck clks) (condClks cnd)) cnds ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    MAP (eval t o compCondition clks «clks») cnds =
    MAP (SOME o (λx. ValWord 1w)) cnds
Proof
  Induct
  >- rw [] >>
  rpt gen_tac >>
  strip_tac >>
  fs [] >>
  drule comp_condition_true_correct >>
  fs [] >> gvs [] >>
  disch_then drule_all >>
  strip_tac >>
  gs [] >>
  last_x_assum match_mp_tac >>
  gs [] >>
  qexists_tac ‘s’ >>
  gs [] >>
  metis_tac []
QED

Theorem and_ones_eq_one:
  ∀n. word_op And (1w::REPLICATE n 1w) = SOME 1w
Proof
  Induct >>
  rw [] >>
  fs [wordLangTheory.word_op_def]
QED


Theorem comp_conditions_true_correct:
  ∀cnds s m (t:('a,'b) panSem$state) clks clkvals.
    EVERY (λcnd. evalCond s cnd) cnds ∧
    m = dimword (:α) - 1 ∧
    EVERY
    (λcnd.
      EVERY (λe. case (evalExpr s e) of
                 | SOME n => n < m
                 | _ => F) (destCond cnd)) cnds ∧
    EVERY
    (λcnd. EVERY (λck. MEM ck clks) (condClks cnd)) cnds ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    eval t (compConditions clks «clks» cnds) = SOME (ValWord 1w)
Proof
  rw [] >>
  drule map_comp_conditions_true_correct >>
  gs [] >>
  disch_then drule_all >>
  strip_tac >>
  pop_assum mp_tac >>
  rpt (pop_assum kall_tac) >>
  MAP_EVERY qid_spec_tac [‘t’,‘clks’,‘cnds’] >>
  Induct >> rw []
  >- (
    fs [compConditions_def] >>
    fs [eval_def]) >>
  fs [compConditions_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  fs [GSYM MAP_MAP_o] >>
  fs [GSYM opt_mmap_eq_some] >>
  ‘MAP (λx. ValWord 1w) cnds =
   REPLICATE (LENGTH cnds) (ValWord 1w)’ by (
    once_rewrite_tac [GSYM map_replicate] >>
    once_rewrite_tac [GSYM map_replicate] >>
    once_rewrite_tac [GSYM map_replicate] >>
    rewrite_tac  [MAP_MAP_o] >>
    rewrite_tac [MAP_EQ_EVERY2] >>
    fs [LIST_REL_EL_EQN] >>
    rw [] >> fs [] >>
    ‘EL n (REPLICATE (LENGTH cnds) (1:num)) = 1’ by (
      match_mp_tac EL_REPLICATE >>
      fs []) >>
    fs []) >>
  fs [] >>
  rewrite_tac [ETA_AX] >>
  gs [] >>
  metis_tac [and_ones_eq_one]
QED


Theorem pickTerm_output_cons_correct:
  ∀s out cnds tclks dest wt s' t (clkvals:'a v list) clks tms m.
    EVERY (λcnd. evalCond s cnd) cnds ∧
    m = dimword (:'a) - 1 ∧
    evalTerm s NONE (Tm (Output out) cnds tclks dest wt) s' ∧
    EVERY
    (λcnd.
      EVERY (λe. case (evalExpr s e) of
                 | SOME n => n < m
                 | _ => F) (destCond cnd)) cnds ∧
    EVERY
    (λcnd. EVERY (λck. MEM ck clks) (condClks cnd)) cnds ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks m ∧
    time_range wt m ∧
    valid_clks clks tclks wt ∧
    FLOOKUP t.locals «event» = SOME (ValWord 0w) ∧
    num_to_str dest IN FDOM t.code ∧
     well_behaved_ffi (num_to_str out) t
                      (w2n (ffiBufferSize:'a word)) (dimword (:α)) ⇒
    ∃bytes.
      evaluate (compTerms clks «clks» «event» (Tm (Output out) cnds tclks dest wt::tms), t) =
      (SOME (Return (retVal s clks tclks wt dest)),
       t with
         <|locals :=
           restore_from t FEMPTY [«len2»; «ptr2»; «len1»; «ptr1»;
                                  «waitTimes»; «newClks»; «wakeUpAt»; «waitSet»];
           memory := write_bytearray t.base_addr bytes t.memory t.memaddrs t.be;
           ffi := nffi_state t out bytes|>)
Proof
  rpt gen_tac >>
  rpt strip_tac >>
  drule_all comp_conditions_true_correct >>
  strip_tac >>
  fs [compTerms_def] >>
  fs [pick_term_def] >>
  once_rewrite_tac [evaluate_def] >>
  gs [timeLangTheory.termConditions_def,
      eval_def,OPT_MMAP_def, ETA_AX, timeLangTheory.termAction_def] >>
  gs [event_match_def,compAction_def, eval_def, asmTheory.word_cmp_def,
      wordLangTheory.word_op_def] >>
  drule comp_output_term_correct >>
  gvs []
QED


Theorem pickTerm_input_cons_correct:
  ∀s n cnds tclks dest wt s' t (clkvals:'a v list) clks tms m.
    EVERY (λcnd. evalCond s cnd) cnds ∧
    evalTerm s (SOME n) (Tm (Input n) cnds tclks dest wt) s' ∧
    m = dimword (:α) - 1 ∧
    EVERY
    (λcnd.
      EVERY (λe. case (evalExpr s e) of
                 | SOME n => n < m
                 | _ => F) (destCond cnd)) cnds ∧
    EVERY
    (λcnd. EVERY (λck. MEM ck clks) (condClks cnd)) cnds ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ∧
    maxClksSize clkvals ∧
    clock_bound s.clocks clks m ∧
    time_range wt m ∧
    valid_clks clks tclks wt ∧
    FLOOKUP t.locals «event» = SOME (ValWord (n2w (n + 1))) ∧
    n + 1 < dimword (:α) ∧
    num_to_str dest IN FDOM t.code ⇒
    evaluate (compTerms clks «clks» «event» (Tm (Input n) cnds tclks dest wt::tms), t) =
    (SOME (Return (retVal s clks tclks wt dest)),
     t with locals :=
     restore_from t FEMPTY [«waitTimes»; «newClks»; «wakeUpAt»; «waitSet»])
Proof
  rpt gen_tac >>
  rpt strip_tac >>
  drule_all comp_conditions_true_correct >>
  strip_tac >>
  fs [compTerms_def] >>
  fs [pick_term_def] >>
  once_rewrite_tac [evaluate_def] >>
  gs [timeLangTheory.termConditions_def,
      eval_def,OPT_MMAP_def, ETA_AX, timeLangTheory.termAction_def] >>
  gs [event_match_def,compAction_def, eval_def, asmTheory.word_cmp_def,
      wordLangTheory.word_op_def] >>
  drule comp_input_term_correct >>
  gvs []
QED


Theorem comp_condition_false_correct:
  ∀s cnd m (t:('a,'b) panSem$state) clks clkvals.
    ~(evalCond s cnd) ∧
    m = dimword (:α) - 1 ∧
    EVERY (λe. case (evalExpr s e) of
               | SOME n => n < m
               | _ => F) (destCond cnd) ∧
    EVERY (λck. MEM ck clks) (condClks cnd) ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    eval t (compCondition clks «clks» cnd) = SOME (ValWord 0w)
Proof
  rw [] >>
  cases_on ‘cnd’ >>
  fs [evalCond_def, timeLangTheory.condClks_def,
      timeLangTheory.destCond_def, timeLangTheory.clksOfExprs_def] >>
  every_case_tac >> fs []
  >- (
   dxrule comp_exp_correct >>
   disch_then
   (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
   impl_tac
   >- (
     fs [] >>
     drule exprClks_accumulates >>
     fs []) >>
   strip_tac >>
   dxrule comp_exp_correct >>
   disch_then
   (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
   impl_tac
   >- (
    fs [EVERY_MEM] >>
    rw [] >>
    fs [] >>
    drule exprClks_sublist_accum >>
    fs []) >>
   strip_tac >>
   fs [compCondition_def] >>
   fs [eval_def, OPT_MMAP_def] >>
   gs [] >>
   fs [asmTheory.word_cmp_def] >>
   gs [word_lo_n2w] >>
   fs [wordLangTheory.word_op_def]) >>
  dxrule comp_exp_correct >>
  disch_then
  (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
  impl_tac
  >- (
    fs [] >>
    drule exprClks_accumulates >>
    fs []) >>
  strip_tac >>
  dxrule comp_exp_correct >>
  disch_then
  (qspecl_then [‘clks’, ‘t’, ‘clkvals’] mp_tac) >>
  impl_tac
  >- (
    fs [EVERY_MEM] >>
    rw [] >>
    fs [] >>
    drule exprClks_sublist_accum >>
    fs []) >>
  strip_tac >>
  fs [compCondition_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  gs [] >>
  fs [asmTheory.word_cmp_def] >>
  gs [word_lo_n2w]
QED


Theorem comp_conditions_false_correct:
  ∀cnds s m (t:('a,'b) panSem$state) clks clkvals.
    ~EVERY (λcnd. evalCond s cnd) cnds ∧
    m = dimword (:α) - 1 ∧
    EVERY (λcnd. EVERY (λe. ∃t. evalExpr s e = SOME t) (destCond cnd)) cnds ∧
    EVERY
    (λcnd.
      EVERY (λe. case (evalExpr s e) of
                 | SOME n => n < m
                 | _ => F) (destCond cnd)) cnds ∧
    EVERY
    (λcnd. EVERY (λck. MEM ck clks) (condClks cnd)) cnds ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ⇒
    eval t (compConditions clks «clks» cnds) = SOME (ValWord 0w)
Proof
  Induct
  >- (
    rw [] >>
    fs []) >>
  rpt gen_tac >>
  strip_tac >>
  fs []
  >- (
  imp_res_tac comp_condition_false_correct >>
  cases_on ‘EVERY (λcnd. evalCond s cnd) cnds’
  >- (
    imp_res_tac comp_conditions_true_correct >>
    fs [compConditions_def] >>
    gs [eval_def, OPT_MMAP_def, ETA_AX] >>
    pop_assum mp_tac >>
    rpt (pop_assum kall_tac) >>
    MAP_EVERY qid_spec_tac [‘t’,‘clks’,‘cnds’] >>
    Induct >> rw []
    >- (
      fs [compConditions_def] >>
      fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def]) >>
    gs [compConditions_def, eval_def, OPT_MMAP_def] >>
    every_case_tac >> gs [] >>
    rveq >> gs [] >>
    every_case_tac >> gs [wordLangTheory.word_op_def] >>
    rveq >> gs [] >>
    metis_tac [EVERY_NOT_EXISTS]) >>
  fs []  >>
  gvs [] >>
  last_x_assum drule_all >>
  strip_tac >>
  drule comp_condition_false_correct >>
  gvs [] >>
  disch_then drule_all >>
  strip_tac >>
  fs [compConditions_def] >>
  fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def] >>
  pop_assum mp_tac >>
  rpt (pop_assum kall_tac) >>
  MAP_EVERY qid_spec_tac [‘t’,‘clks’,‘cnds’] >>
  Induct >> rw []
  >- (
    fs [compConditions_def] >>
    fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def]) >>
  gs [compConditions_def, eval_def, OPT_MMAP_def] >>
  every_case_tac >> gs [] >>
  rveq >> gs [] >>
  every_case_tac >> gs [wordLangTheory.word_op_def] >>
  rveq >> gs [] >>
  metis_tac [EVERY_NOT_EXISTS]) >>
  gvs [] >>
  last_x_assum drule_all >>
  strip_tac >>
  cases_on ‘evalCond s h’
  >- (
  drule comp_condition_true_correct >>
  gvs [] >>
    disch_then drule_all >>
    strip_tac >>
    fs [compConditions_def] >>
    fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    pop_assum mp_tac >>
    rpt (pop_assum kall_tac) >>
    MAP_EVERY qid_spec_tac [‘t’,‘clks’,‘cnds’] >>
    Induct >> rw []
    >- (
    fs [compConditions_def] >>
    fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def]) >>
    gs [compConditions_def, eval_def, OPT_MMAP_def] >>
    every_case_tac >> gs [] >>
    rveq >> gs [] >>
    every_case_tac >> gs [wordLangTheory.word_op_def] >>
    rveq >> gs [] >>
    metis_tac [EVERY_NOT_EXISTS]) >>
  drule comp_condition_false_correct >>
  gvs [] >>
  disch_then drule_all >>
  strip_tac >>
  fs [compConditions_def] >>
  fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  pop_assum mp_tac >>
  rpt (pop_assum kall_tac) >>
  MAP_EVERY qid_spec_tac [‘t’,‘clks’,‘cnds’] >>
  Induct >> rw []
  >- (
  fs [compConditions_def] >>
  fs [OPT_MMAP_def, eval_def, wordLangTheory.word_op_def]) >>
  gs [compConditions_def, eval_def, OPT_MMAP_def] >>
  every_case_tac >> gs [] >>
  rveq >> gs [] >>
  every_case_tac >> gs [wordLangTheory.word_op_def] >>
  rveq >> gs [] >>
  metis_tac [EVERY_NOT_EXISTS]
QED


Theorem pickTerm_panic_correct:
  ∀tms s t (clkvals:'a v list) clks m.
    EVERY
    (λtm.
      EVERY
      (λcnd. EVERY (λe. ∃t. evalExpr s e = SOME t) (destCond cnd))
      (termConditions tm)) tms ∧
    EVERY (λtm. EXISTS ($~ ∘ (λcnd. evalCond s cnd)) (termConditions tm))
          tms ∧
    m = dimword (:'a) - 1 ∧
    conds_eval_lt_dimword m s tms ∧
    conds_clks_mem_clks clks tms ∧
    FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
    equiv_val s.clocks clks clkvals ∧
    (∃v. FLOOKUP t.eshapes «panic» = SOME One) ∧
    (∃v. FLOOKUP t.locals «event» = SOME (ValWord v)) ⇒
      evaluate (compTerms clks «clks» «event» tms, t) =
      (SOME (Exception «panic» (ValWord 0w)), empty_locals t)
Proof
  Induct >> rw []
  >- (
    gs [compTerms_def] >>
    once_rewrite_tac [evaluate_def] >>
    gs [eval_def, shape_of_def, panLangTheory.size_of_shape_def]) >>
  cases_on ‘h’ >>
  fs [compTerms_def] >>
  once_rewrite_tac [evaluate_def] >>
  fs [timeLangTheory.termConditions_def, timeLangTheory.termAction_def] >>
  fs [pick_term_def] >>
  ‘eval t (compConditions clks «clks» l) = SOME (ValWord 0w)’ by (
    match_mp_tac comp_conditions_false_correct >>
    gs [] >>
    qexists_tac ‘s’ >>
    gs [conds_eval_lt_dimword_def, tm_conds_eval_limit_def,
        timeLangTheory.termConditions_def, conds_clks_mem_clks_def]) >>
  gs [eval_def, OPT_MMAP_def] >>
  cases_on ‘i’ >>
  fs [event_match_def] >>
  gs [eval_def,compAction_def, asmTheory.word_cmp_def, wordLangTheory.word_op_def] >>
  last_x_assum (qspecl_then [‘s’, ‘t’, ‘clkvals’, ‘clks’] mp_tac) >>
  (impl_tac >- gs [conds_eval_lt_dimword_def, conds_clks_mem_clks_def] >>
  gs [])
QED

Theorem pick_term_thm:
  ∀s m e tms s' lbl.
    pickTerm s m e tms s' lbl ⇒
    (∀(t :('a, 'b) panSem$state) clks clkvals.
       m = dimword (:α) - 1  ∧
       conds_clks_mem_clks clks tms ∧
       terms_valid_clocks clks tms ∧
       locs_in_code t.code tms ∧
       FLOOKUP t.locals «clks» = SOME (Struct clkvals) ∧
       EVERY (λck. ∃n. FLOOKUP s.clocks ck = SOME n) clks ∧
       equiv_val s.clocks clks clkvals ∧
       maxClksSize clkvals ∧
       out_signals_ffi t tms ⇒
       (e = NONE ∧ (∃os. lbl = LAction (Output os)) ∧
        FLOOKUP t.locals «event» = SOME (ValWord 0w) ⇒
        ∃out cnds tclks dest wt.
          MEM (Tm (Output out) cnds tclks dest wt) tms ∧
          EVERY (λcnd. evalCond s cnd) cnds ∧
          evalTerm s NONE
                   (Tm (Output out) cnds tclks dest wt) s' ∧
          ∃bytes.
            evaluate (compTerms clks «clks» «event» tms, t) =
            (SOME (Return (retVal s clks tclks wt dest)),
             t with
               <|locals :=
                 restore_from t FEMPTY [«len2»; «ptr2»; «len1»; «ptr1»;
                                        «waitTimes»; «newClks»; «wakeUpAt»; «waitSet»];
                 memory := write_bytearray t.base_addr bytes t.memory t.memaddrs t.be;
                 ffi := nffi_state t out bytes|>)) ∧
       (∀n. e = SOME n ∧ lbl = LAction (Input n) ∧ n+1 < dimword (:'a) ∧
            FLOOKUP t.locals «event» = SOME (ValWord (n2w (n+1))) ⇒
            ∃cnds tclks dest wt.
              MEM (Tm (Input n) cnds tclks dest wt) tms ∧
              EVERY (λcnd. evalCond s cnd) cnds ∧
              evalTerm s (SOME n)
                       (Tm (Input n) cnds tclks dest wt) s' ∧
              evaluate (compTerms clks «clks» «event» tms, t) =
              (SOME (Return (retVal s clks tclks wt dest)),
               t with locals :=
               restore_from t FEMPTY [«waitTimes»; «newClks»; «wakeUpAt»; «waitSet»])) ∧
       (e = NONE ∧ lbl = LPanic PanicTimeout ∧
        FLOOKUP t.locals «event» = SOME (ValWord 0w) ∧
        FLOOKUP t.eshapes «panic» = SOME One  ⇒
        evaluate (compTerms clks «clks» «event» tms, t) =
        (SOME (Exception «panic» (ValWord 0w)),empty_locals t)) ∧
       (∀n.
          e = SOME n ∧ lbl = LPanic (PanicInput n) ∧ n+1 < dimword (:'a) ∧
          FLOOKUP t.locals «event» = SOME (ValWord (n2w (n+1))) ∧
          FLOOKUP t.eshapes «panic» = SOME One  ⇒
          evaluate (compTerms clks «clks» «event» tms, t) =
            (SOME (Exception «panic» (ValWord 0w)),empty_locals t)))
Proof
  ho_match_mp_tac pickTerm_ind >>
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    fs [] >>
    rw [] >>
    MAP_EVERY qexists_tac
              [‘cnds’, ‘clks’, ‘dest’, ‘diffs’] >>
    fs [] >>
    match_mp_tac pickTerm_input_cons_correct >>
    qexists_tac ‘s'’ >>
    qexists_tac ‘clkvals’ >>
    gvs [] >>
    conj_tac
    >- (
      gs [conds_eval_lt_dimword_def, tm_conds_eval_limit_def,
          timeLangTheory.termConditions_def] >>
      gs [EVERY_MEM] >>
      rw [] >>
      first_x_assum drule >>
      gs [] >>
      disch_then drule >>
      TOP_CASE_TAC >> gs []) >>
    conj_tac
    >- gs [conds_clks_mem_clks_def, timeLangTheory.termConditions_def] >>
    conj_tac
    >- (
      gs [clock_bound_def, max_clocks_def, EVERY_MEM] >>
      rw [] >>
      first_x_assum drule >>
      strip_tac >> gs [] >>
      last_x_assum drule >>
      gs []) >>
    conj_tac
    >- (
      gs [terms_time_range_def, term_time_range_def, time_range_def,
          timeLangTheory.termWaitTimes_def] >>
      gs [EVERY_MEM] >>
      rw [] >>
      first_x_assum drule >>
      strip_tac >>
      cases_on ‘e’ >>
      gs []) >>
    conj_tac
    >- gs [terms_valid_clocks_def, timeLangTheory.termClks_def,
           timeLangTheory.termWaitTimes_def] >>
    gs [locs_in_code_def, timeLangTheory.termDest_def]) >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    fs [] >>
    rw [] >>
    MAP_EVERY qexists_tac
              [‘out_signal’, ‘cnds’, ‘clks’, ‘dest’, ‘diffs’] >>
    fs [] >>
    match_mp_tac pickTerm_output_cons_correct >>
    qexists_tac ‘s'’ >>
    qexists_tac ‘clkvals’ >>
    gvs [] >>
    conj_tac
    >- gs [conds_eval_lt_dimword_def, tm_conds_eval_limit_def,
           timeLangTheory.termConditions_def] >>
    conj_tac
    >- gs [conds_clks_mem_clks_def, timeLangTheory.termConditions_def] >>
    conj_tac
    >- (
      gs [clock_bound_def, max_clocks_def, EVERY_MEM] >>
      rw [] >>
      first_x_assum drule >>
      strip_tac >> gs [] >>
      last_x_assum drule >>
      gs []) >>
    conj_tac
    >- gs [terms_time_range_def, term_time_range_def,
           timeLangTheory.termWaitTimes_def] >>
    conj_tac
    >- gs [terms_valid_clocks_def, timeLangTheory.termClks_def,
           timeLangTheory.termWaitTimes_def] >>
    conj_tac
    >- gs [locs_in_code_def, timeLangTheory.termDest_def] >>
    gs [out_signals_ffi_def, timeLangTheory.terms_out_signals_def]) >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    fs [] >>
    cases_on ‘e’ >> fs []
    >- (
      rw [] >>
      fs []
      >- (
        last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
        gs [] >>
        impl_tac
        >- (
          gs [conds_eval_lt_dimword_def, conds_clks_mem_clks_def,
              terms_time_range_def, terms_valid_clocks_def,
              locs_in_code_def, out_signals_ffi_def, input_terms_actions_def] >>
          cases_on ‘ioAction’ >>
          gs [timeLangTheory.terms_out_signals_def,
              timeLangTheory.terms_in_signals_def]) >>
        strip_tac >>
        MAP_EVERY qexists_tac
                  [‘out’, ‘cnds'’, ‘tclks’, ‘dest'’, ‘wt’] >>
        fs [] >>
        qexists_tac ‘bytes’ >>
        (* we can have a separate theorem *)
        fs [compTerms_def] >>
        fs [pick_term_def] >>
        once_rewrite_tac [evaluate_def] >>
        fs [timeLangTheory.termConditions_def] >>
        ‘eval t (compConditions clks' «clks» cnds) = SOME (ValWord 0w)’ by (
          match_mp_tac comp_conditions_false_correct >>
          gs [] >>
          qexists_tac ‘s’ >>
          gvs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
              tm_conds_eval_limit_def,
              timeLangTheory.termConditions_def]) >>
        gs [eval_def, OPT_MMAP_def] >>
        fs [timeLangTheory.termAction_def] >>
        cases_on ‘ioAction’ >>
        fs [event_match_def] >>
        gs [eval_def,compAction_def,
            asmTheory.word_cmp_def,
            wordLangTheory.word_op_def]) >>
      last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
      gs [] >>
      impl_tac
      >- (
        gs [conds_clks_mem_clks_def, terms_valid_clocks_def, locs_in_code_def,
            out_signals_ffi_def] >>
        cases_on ‘ioAction’ >>
        gs [timeLangTheory.terms_out_signals_def]) >>
      strip_tac >>
      fs [compTerms_def] >>
      once_rewrite_tac [evaluate_def] >>
      fs [timeLangTheory.termConditions_def, timeLangTheory.termAction_def] >>
      fs [pick_term_def] >>
      ‘eval t (compConditions clks' «clks» cnds) = SOME (ValWord 0w)’ by (
          match_mp_tac comp_conditions_false_correct >>
          gs [] >>
          qexists_tac ‘s’ >>
          gvs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
              tm_conds_eval_limit_def,
              timeLangTheory.termConditions_def]) >>
      gs [eval_def, OPT_MMAP_def] >>
      cases_on ‘ioAction’ >>
      fs [event_match_def] >>
      gs [eval_def,compAction_def,
          asmTheory.word_cmp_def,
          wordLangTheory.word_op_def]) >>
    rw [] >>
    fs []
    >- (
    last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    gs [] >>
    impl_tac
    >- (
    gs [conds_eval_lt_dimword_def, conds_clks_mem_clks_def,
        terms_time_range_def, terms_valid_clocks_def,
        locs_in_code_def, out_signals_ffi_def, input_terms_actions_def] >>
    cases_on ‘ioAction’ >>
    gs [timeLangTheory.terms_out_signals_def,
        timeLangTheory.terms_in_signals_def]) >>
    strip_tac >>
    MAP_EVERY qexists_tac
              [‘cnds'’, ‘tclks’, ‘dest'’, ‘wt’] >>
    fs [] >>
    fs [compTerms_def] >>
    fs [pick_term_def] >>
    once_rewrite_tac [evaluate_def] >>
    fs [timeLangTheory.termConditions_def] >>
    ‘eval t (compConditions clks' «clks» cnds) = SOME (ValWord 0w)’ by (
      match_mp_tac comp_conditions_false_correct >>
      gs [] >>
      qexists_tac ‘s’ >>
      gvs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
          tm_conds_eval_limit_def,
          timeLangTheory.termConditions_def]) >>
    gs [eval_def, OPT_MMAP_def] >>
    fs [timeLangTheory.termAction_def] >>
    cases_on ‘ioAction’ >>
    fs [event_match_def] >>
    gs [eval_def,compAction_def, asmTheory.word_cmp_def, wordLangTheory.word_op_def]) >>
    last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    gs [] >>
    impl_tac
    >- (
    gs [conds_eval_lt_dimword_def, conds_clks_mem_clks_def,
        terms_time_range_def, terms_valid_clocks_def,
        locs_in_code_def, out_signals_ffi_def, input_terms_actions_def] >>
    cases_on ‘ioAction’ >>
    gs [timeLangTheory.terms_out_signals_def,
        timeLangTheory.terms_in_signals_def]) >>
    strip_tac >>
    fs [compTerms_def] >>
    once_rewrite_tac [evaluate_def] >>
    fs [timeLangTheory.termConditions_def, timeLangTheory.termAction_def] >>
    fs [pick_term_def] >>
    ‘eval t (compConditions clks' «clks» cnds) = SOME (ValWord 0w)’ by (
      match_mp_tac comp_conditions_false_correct >>
      gs [] >>
      qexists_tac ‘s’ >>
      gvs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
          tm_conds_eval_limit_def,
          timeLangTheory.termConditions_def]) >>
    gs [eval_def, OPT_MMAP_def] >>
    cases_on ‘ioAction’ >>
    fs [event_match_def] >>
    gs [eval_def,compAction_def,
        asmTheory.word_cmp_def,
        wordLangTheory.word_op_def]) >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    rw [] >>
    gs []
    >- (
      last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
      gs [] >>
      impl_tac
      >- (
      gs [conds_eval_lt_dimword_def, conds_clks_mem_clks_def,
          terms_time_range_def, terms_valid_clocks_def,
          locs_in_code_def, out_signals_ffi_def, input_terms_actions_def] >>
      gs [timeLangTheory.terms_out_signals_def, timeLangTheory.terms_in_signals_def]) >>
      strip_tac >>
      MAP_EVERY qexists_tac
                [‘out’,‘cnds'’, ‘tclks’, ‘dest'’, ‘wt’] >>
      fs [] >>
      fs [compTerms_def] >>
      fs [pick_term_def] >>
      fs [timeLangTheory.termConditions_def,
          timeLangTheory.termAction_def] >>
      fs [event_match_def, compAction_def] >>
      once_rewrite_tac [evaluate_def] >>
      fs [eval_def, OPT_MMAP_def] >>
      cases_on ‘EVERY (λcnd. evalCond s cnd) cnds’
      >- (
        drule comp_conditions_true_correct >>
        disch_then (qspecl_then [‘dimword (:α) − 1 ’, ‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
        impl_tac
        >- (
          gvs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
              tm_conds_eval_limit_def,
              timeLangTheory.termConditions_def]) >>
        strip_tac >> fs [] >>
        gs [asmTheory.word_cmp_def] >>
        ‘(in_signal + 1) MOD dimword (:α) = in_signal + 1’ by (
          match_mp_tac LESS_MOD >>
          gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def]) >>
        fs [] >>
        fs [wordLangTheory.word_op_def] >>
        metis_tac []) >>
      drule comp_conditions_false_correct >>
      disch_then (qspecl_then [‘dimword (:α) − 1 ’, ‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
      impl_tac
      >- (
        gvs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
            tm_conds_eval_limit_def,
            timeLangTheory.termConditions_def] >>
        gs [EVERY_MEM] >>
        rw [] >>
        res_tac  >> gs [] >>
        every_case_tac >> gs []) >>
      strip_tac >> fs [] >>
      gs [asmTheory.word_cmp_def] >>
      ‘(in_signal + 1) MOD dimword (:α) = in_signal + 1’ by (
        match_mp_tac LESS_MOD >>
        gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def]) >>
        fs [] >>
      fs [wordLangTheory.word_op_def] >>
      metis_tac [])
    >- (
    last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    gs [] >>
    impl_tac
    >- (
        gs [conds_clks_mem_clks_def, terms_valid_clocks_def, locs_in_code_def,
            out_signals_ffi_def] >>
        gs [timeLangTheory.terms_out_signals_def]) >>
    strip_tac >>
    MAP_EVERY qexists_tac
              [‘cnds'’, ‘tclks’, ‘dest'’, ‘wt’] >>
    fs [] >>
    fs [compTerms_def] >>
    fs [pick_term_def] >>
    fs [timeLangTheory.termConditions_def,
        timeLangTheory.termAction_def] >>
    fs [event_match_def, compAction_def] >>
    once_rewrite_tac [evaluate_def] >>
    fs [eval_def, OPT_MMAP_def] >>
    cases_on ‘EVERY (λcnd. evalCond s cnd) cnds’
    >- (
    drule comp_conditions_true_correct >>
    disch_then (qspecl_then [‘dimword (:α) − 1 ’, ‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    impl_tac
    >- (
      gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
          tm_conds_eval_limit_def,
          timeLangTheory.termConditions_def]) >>
    strip_tac >> fs [] >>
    gs [asmTheory.word_cmp_def] >>
    ‘(in_signal + 1) MOD dimword (:α) = in_signal + 1’ by (
      match_mp_tac LESS_MOD >>
      gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def]) >>
    fs [] >>
    fs [wordLangTheory.word_op_def] >>
    metis_tac []) >>
    drule comp_conditions_false_correct >>
    disch_then (qspecl_then [‘dimword (:α) − 1 ’, ‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    impl_tac
    >- (
     gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
         tm_conds_eval_limit_def,
         timeLangTheory.termConditions_def] >>
     gs [EVERY_MEM] >>
     rw [] >>
     res_tac  >> gs [] >>
     every_case_tac >> gs []) >>
    strip_tac >> fs [] >>
    gs [asmTheory.word_cmp_def] >>
    ‘(in_signal + 1) MOD dimword (:α) = in_signal + 1’ by (
      match_mp_tac LESS_MOD >>
      gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def]) >>
    fs [] >>
    fs [wordLangTheory.word_op_def] >>
    metis_tac [])
    >- (
    last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    gs [] >>
    impl_tac
    >- (
        gs [conds_clks_mem_clks_def, terms_valid_clocks_def, locs_in_code_def,
            out_signals_ffi_def] >>
        gs [timeLangTheory.terms_out_signals_def]) >>
    strip_tac >>
    fs [] >>
    fs [compTerms_def] >>
    fs [pick_term_def] >>
    fs [timeLangTheory.termConditions_def,
        timeLangTheory.termAction_def] >>
    fs [event_match_def, compAction_def] >>
    once_rewrite_tac [evaluate_def] >>
    fs [eval_def, OPT_MMAP_def] >>
    cases_on ‘EVERY (λcnd. evalCond s cnd) cnds’
    >- (
    drule comp_conditions_true_correct >>
    disch_then (qspecl_then [‘dimword (:α) − 1 ’, ‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    impl_tac
    >- (
      gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
          tm_conds_eval_limit_def,
          timeLangTheory.termConditions_def]) >>
    strip_tac >> fs [] >>
    gs [asmTheory.word_cmp_def] >>
    ‘(in_signal + 1) MOD dimword (:α) = in_signal + 1’ by (
      match_mp_tac LESS_MOD >>
      gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def]) >>
    fs [] >>
    fs [wordLangTheory.word_op_def] >>
    metis_tac []) >>
    drule comp_conditions_false_correct >>
    disch_then (qspecl_then [‘dimword (:α) − 1 ’, ‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    impl_tac
    >- (
     gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
         tm_conds_eval_limit_def,
         timeLangTheory.termConditions_def] >>
     gs [EVERY_MEM] >>
     rw [] >>
     res_tac  >> gs [] >>
     every_case_tac >> gs []) >>
    strip_tac >> fs [] >>
    gs [asmTheory.word_cmp_def] >>
    ‘(in_signal + 1) MOD dimword (:α) = in_signal + 1’ by (
      match_mp_tac LESS_MOD >>
      gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def]) >>
    fs [] >>
    fs [wordLangTheory.word_op_def] >>
    metis_tac []) >>
    last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    gs [] >>
    impl_tac
    >- (
    gs [conds_clks_mem_clks_def, terms_valid_clocks_def, locs_in_code_def,
        out_signals_ffi_def] >>
    gs [timeLangTheory.terms_out_signals_def]) >>
    strip_tac >>
    fs [] >>
    fs [compTerms_def] >>
    fs [pick_term_def] >>
    fs [timeLangTheory.termConditions_def,
        timeLangTheory.termAction_def] >>
    fs [event_match_def, compAction_def] >>
    once_rewrite_tac [evaluate_def] >>
    fs [eval_def, OPT_MMAP_def] >>
    cases_on ‘EVERY (λcnd. evalCond s cnd) cnds’
    >- (
    drule comp_conditions_true_correct >>
    disch_then (qspecl_then [‘dimword (:α) − 1 ’, ‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    impl_tac
    >- (
      gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
          tm_conds_eval_limit_def,
          timeLangTheory.termConditions_def]) >>
    strip_tac >> fs [] >>
    gs [asmTheory.word_cmp_def] >>
    ‘(in_signal + 1) MOD dimword (:α) = in_signal + 1’ by (
      match_mp_tac LESS_MOD >>
      gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def]) >>
    fs [] >>
    fs [wordLangTheory.word_op_def] >>
    metis_tac []) >>
    drule comp_conditions_false_correct >>
    disch_then (qspecl_then [‘dimword (:α) − 1 ’, ‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    impl_tac
    >- (
     gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
         tm_conds_eval_limit_def,
         timeLangTheory.termConditions_def] >>
     gs [EVERY_MEM] >>
     rw [] >>
     res_tac  >> gs [] >>
     every_case_tac >> gs []) >>
    strip_tac >> fs [] >>
    gs [asmTheory.word_cmp_def] >>
    ‘(in_signal + 1) MOD dimword (:α) = in_signal + 1’ by (
      match_mp_tac LESS_MOD >>
      gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def]) >>
    fs [] >>
    fs [wordLangTheory.word_op_def] >>
    metis_tac []) >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    rw [] >>
    gs []
    >- (
    last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    gs [] >>
  impl_tac
    >- (
      gs [conds_clks_mem_clks_def, terms_valid_clocks_def, locs_in_code_def,
          out_signals_ffi_def] >>
      gs [timeLangTheory.terms_out_signals_def]) >>
    strip_tac >>
  MAP_EVERY qexists_tac
            [‘cnds'’, ‘tclks’, ‘dest'’, ‘wt’] >>
  fs [] >>
  fs [compTerms_def] >>
  fs [pick_term_def] >>
  fs [timeLangTheory.termConditions_def,
      timeLangTheory.termAction_def] >>
  fs [event_match_def, compAction_def] >>
  once_rewrite_tac [evaluate_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  cases_on ‘EVERY (λcnd. evalCond s cnd) cnds’
  >- (
    drule comp_conditions_true_correct >>
    disch_then (qspecl_then [‘dimword (:α) − 1 ’, ‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    impl_tac
    >- (
      gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
          tm_conds_eval_limit_def,
          timeLangTheory.termConditions_def]) >>
    strip_tac >> fs [] >>
    gs [asmTheory.word_cmp_def] >>
    fs [wordLangTheory.word_op_def]) >>
  drule comp_conditions_false_correct >>
  disch_then (qspecl_then [‘dimword (:α) − 1 ’, ‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
  impl_tac
  >- (
    gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
        tm_conds_eval_limit_def,
        timeLangTheory.termConditions_def] >>
    gs [EVERY_MEM] >>
    rw [] >>
    res_tac  >> gs [] >>
    every_case_tac >> gs []) >>
  strip_tac >> fs [] >>
  gs [asmTheory.word_cmp_def] >>
    fs [wordLangTheory.word_op_def]) >>
    last_x_assum (qspecl_then [‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    gs [] >>
    impl_tac
    >- (
      gs [conds_clks_mem_clks_def, terms_valid_clocks_def, locs_in_code_def,
          out_signals_ffi_def] >>
      gs [timeLangTheory.terms_out_signals_def]) >>
    strip_tac >>
  fs [] >>
  fs [compTerms_def] >>
  fs [pick_term_def] >>
  fs [timeLangTheory.termConditions_def,
      timeLangTheory.termAction_def] >>
  fs [event_match_def, compAction_def] >>
  once_rewrite_tac [evaluate_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  cases_on ‘EVERY (λcnd. evalCond s cnd) cnds’
  >- (
    drule comp_conditions_true_correct >>
    disch_then (qspecl_then [‘dimword (:α) − 1 ’, ‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
    impl_tac
    >- (
      gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
          tm_conds_eval_limit_def,
          timeLangTheory.termConditions_def]) >>
    strip_tac >> fs [] >>
    gs [asmTheory.word_cmp_def] >>
    fs [wordLangTheory.word_op_def]) >>
  drule comp_conditions_false_correct >>
  disch_then (qspecl_then [‘dimword (:α) − 1 ’, ‘t’, ‘clks'’, ‘clkvals’] mp_tac) >>
  impl_tac
  >- (
    gs [conds_clks_mem_clks_def, conds_eval_lt_dimword_def,
        tm_conds_eval_limit_def,
        timeLangTheory.termConditions_def] >>
    gs [EVERY_MEM] >>
    rw [] >>
    res_tac  >> gs [] >>
    every_case_tac >> gs []) >>
  strip_tac >> fs [] >>
  gs [asmTheory.word_cmp_def] >>
    fs [wordLangTheory.word_op_def]) >>
  strip_tac >>
  rpt gen_tac
  >- (
  strip_tac >>
  rw [] >>
  fs [compTerms_def, evaluate_def, eval_def, shape_of_def, panLangTheory.size_of_shape_def]) >>
  strip_tac >>
  rw [] >>
  fs [compTerms_def, evaluate_def, eval_def, shape_of_def, panLangTheory.size_of_shape_def]
QED


Theorem pick_term_dest_eq:
  ∀s m e tms s' lbl.
    pickTerm s m e tms s' lbl ⇒
    (e = NONE ⇒
     ((∃out.
         lbl = LAction (Output out)) ⇒
      (case s'.waitTime of
       | NONE => T
       | SOME x => x < m)) ∧
     (∀out cnds tclks dest wt.
       MEM (Tm (Output out) cnds tclks dest wt) tms ∧
       EVERY (λcnd. evalCond s cnd) cnds ∧
       evalTerm s NONE (Tm (Output out) cnds tclks dest wt) s' ⇒
       dest = s'.location ∧ s'.ioAction = SOME (Output out) ∧
       (case wt of [] => s'.waitTime = NONE | _ => ∃nt. s'.waitTime = SOME nt))) ∧
    (∀n.
       e = SOME n ⇒
       n+1 < m ∧
       (lbl = LAction (Input n) ⇒
        (case s'.waitTime of
         | NONE => T
         | SOME x => x < m)) ∧
       (∀cnds tclks dest wt.
          MEM (Tm (Input n) cnds tclks dest wt) tms ∧
          EVERY (λcnd. evalCond s cnd) cnds ∧
          evalTerm s (SOME n) (Tm (Input n) cnds tclks dest wt) s' ⇒
          dest = s'.location ∧
          (case wt of [] => s'.waitTime = NONE | _ => ∃nt. s'.waitTime = SOME nt)))
Proof
  ho_match_mp_tac pickTerm_ind >>
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    fs [] >>
    conj_tac
    >- gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def] >>
    conj_tac
    >- (
      gs [input_terms_actions_def, timeLangTheory.terms_in_signals_def] >>
      TOP_CASE_TAC >>
      gs [evalTerm_cases] >>
      gs [terms_wtimes_ffi_bound_def, timeLangTheory.termClks_def,
          timeLangTheory.termWaitTimes_def] >>
      every_case_tac
      >- (drule calculate_wtime_reset_output_eq >> gs []) >>
      pop_assum mp_tac >>
      pop_assum mp_tac >>
      drule calculate_wtime_reset_output_eq >> gs []) >>
    strip_tac >>
    fs [] >>
    rw [] >>
    fs [evalTerm_cases] >>
    every_case_tac >>
    fs [calculate_wtime_def, list_min_option_def] >>
    every_case_tac >> gs [] >>
    metis_tac []) >>
  strip_tac >>
  rpt gen_tac
  >- (
    strip_tac >>
    fs [] >>
    reverse conj_tac
    >- (
      rw [] >>
      fs [evalTerm_cases] >>
      every_case_tac >>
      gs [calculate_wtime_def, list_min_option_def] >>
      every_case_tac >> gs [] >>
      metis_tac []) >>
    TOP_CASE_TAC >>
    gs [evalTerm_cases] >>
    gs [terms_wtimes_ffi_bound_def, timeLangTheory.termClks_def,
        timeLangTheory.termWaitTimes_def] >>
    every_case_tac
    >- (drule calculate_wtime_reset_output_eq >> gs []) >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    drule calculate_wtime_reset_output_eq >> gs []) >>
  strip_tac >>
  rpt gen_tac
  >- (
   strip_tac >>
   cases_on ‘e’ >> fs [] >>
   rw [] >> fs [] >>
   metis_tac [EVERY_NOT_EXISTS]) >>
  strip_tac >>
  rpt gen_tac
  >- (
   strip_tac >>
   cases_on ‘e’ >> fs [] >>
   rw [] >> fs [] >>
   metis_tac [EVERY_NOT_EXISTS]) >>
  strip_tac >>
  rpt gen_tac
  >- (
   strip_tac >>
   cases_on ‘e’ >> fs [] >>
   rw [] >> fs [] >>
   metis_tac [EVERY_NOT_EXISTS]) >>
  strip_tac >>
  rpt gen_tac
  >- (
   strip_tac >>
   gs [max_clocks_def] >>
   rw [] >> fs [] >>
   metis_tac [EVERY_NOT_EXISTS]) >>
  strip_tac >>
  rw [] >> fs []
QED


(* step theorems *)

Theorem state_rel_imp_time_seq_ffi:
  ∀cks outs s t.
    state_rel cks outs s (t:('a,time_input) panSem$state) ⇒
    time_seq t.ffi.ffi_state (dimword (:'a))
Proof
  rw [state_rel_def] >>
  pairarg_tac >> gs []
QED


Theorem state_rel_imp_ffi_vars:
  ∀cks outs s t.
    state_rel cks outs s (t:('a,time_input) panSem$state) ⇒
    ffi_vars t.locals t.base_addr
Proof
  rw [state_rel_def]
QED


Theorem state_rel_imp_equivs:
  ∀cks outs s t.
    state_rel cks outs s (t:('a,time_input) panSem$state) ⇒
    equivs t.locals s.location s.waitTime
Proof
  rw [state_rel_def]
QED

Theorem time_seq_mono:
  ∀m n f a.
    n ≤ m ∧
    time_seq f a ⇒
    FST (f n) ≤ FST (f m)
Proof
  Induct >>
  rw [] >>
  fs [time_seq_def] >>
  fs [LE] >>
  last_x_assum (qspecl_then [‘n’, ‘f’, ‘a’] mp_tac) >>
  impl_tac
  >- gs [] >>
  strip_tac >>
  ‘FST (f m) ≤ FST (f (SUC m))’ suffices_by gs [] >>
  last_x_assum (qspec_then ‘m’ mp_tac) >>
  gs []
QED



Theorem step_delay_eval_wait_not_zero:
  !t.
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «waitSet» = SOME (ValWord 1w) ∧
    (?tm. FLOOKUP t.locals «sysTime» = SOME (ValWord tm)) ∧
    (?tm. FLOOKUP t.locals «wakeUpAt» = SOME (ValWord tm)) ==>
    ?w.
      eval t wait = SOME (ValWord w) ∧
      w ≠ 0w
Proof
  rw [] >>
  fs [wait_def, eval_def, OPT_MMAP_def] >>
  gs [wordLangTheory.word_op_def] >>
  TOP_CASE_TAC >>
  fs []
QED


Theorem mod_greater_neq:
  tm = (tm + wt) MOD (k:num) ∧
  tm < k ∧ wt < k ∧
  k < tm + wt ⇒ F
Proof
  CCONTR_TAC >> gvs [] >>
  ‘((tm + wt) - k) MOD k = (tm + wt) MOD k’ by
    (irule SUB_MOD >> fs []) >>
  pop_assum (fs o single o GSYM) >>
  ‘tm + wt − k < k’ by gvs [] >>
  fs []
QED


Theorem step_wait_delay_eval_wait_not_zero:
  !(t:('a,'b) panSem$state).
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «waitSet» = SOME (ValWord 0w) ∧
    (?tm. FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w tm)) ∧
          ?wt. FLOOKUP t.locals «wakeUpAt» = SOME (ValWord (n2w (tm + wt))) ∧
               tm < tm + wt ∧
               wt < dimword (:α) ∧
               tm < dimword (:α)) ==>
    ?w.
      eval t wait = SOME (ValWord w) ∧
      w ≠ 0w
Proof
  rw [] >>
  fs [wait_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  gs [active_low_def,
      wordLangTheory.word_op_def] >>
  TOP_CASE_TAC >>
  fs [] >>
  fs [asmTheory.word_cmp_def] >>
  fs [addressTheory.WORD_CMP_NORMALISE] >>
  fs [word_ls_n2w] >>
  ‘wt MOD dimword (:α) = wt’ by (
    match_mp_tac LESS_MOD >> fs []) >>
  ‘tm MOD dimword (:α) = tm’ by (
    match_mp_tac LESS_MOD >> fs []) >>
  fs [] >> rveq >> gs [] >>
  cases_on ‘tm + wt < dimword (:α)’
  >- (
    ‘(tm + wt) MOD dimword (:α) = tm + wt’ by (
      match_mp_tac LESS_MOD >> fs []) >>
    gs []) >>
  gs [NOT_LESS] >>
  gs [LESS_OR_EQ] >>
  metis_tac [mod_greater_neq]
QED


Theorem state_rel_imp_mem_config:
  ∀clks outs io s t.
    state_rel clks outs s t ==>
    mem_config t.memory t.memaddrs t.be t.base_addr
Proof
  rw [state_rel_def]
QED


Theorem state_rel_imp_systime_defined:
  ∀clks outs io s t.
    state_rel clks outs s t ==>
    ∃tm. FLOOKUP t.locals «sysTime» = SOME (ValWord tm)
Proof
  rw [state_rel_def, time_vars_def] >>
  pairarg_tac >> fs []
QED

Theorem state_rel_imp_time_vars:
  ∀clks outs s t.
    state_rel clks outs s t ==>
    time_vars t.locals
Proof
  rw [state_rel_def]
QED

Theorem evaluate_ext_call:
  ∀(t :('a, time_input) panSem$state) res t' outs bytes.
    evaluate (ExtCall «get_time_input» «ptr1» «len1» «ptr2» «len2» ,t) = (res,t') ∧
    read_bytearray t.base_addr (w2n (ffiBufferSize:α word))
                   (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes ∧
    t.ffi = build_ffi (:'a) t.be outs t.ffi.ffi_state t.ffi.io_events ∧
    ffi_vars t.locals t.base_addr ∧ good_dimindex (:'a) ⇒
    res = NONE ∧
    t' = t with
           <| memory := mem_call_ffi (:α) t.memory t.memaddrs t.be t.base_addr t.ffi.ffi_state
            ; ffi := ffi_call_ffi (:α) t.be t.ffi bytes|>
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [good_dimindex_def] >>
  (fs [evaluate_def, ffi_vars_def, read_bytearray_def] >>
   gs [build_ffi_def, ffiTheory.call_FFI_def] >>
   gs [ffiTheory.ffi_state_component_equality] >>
   fs [time_input_def] >>
   drule read_bytearray_LENGTH >>
   strip_tac >>
   fs [length_get_bytes] >>
   fs [ffiBufferSize_def] >>
   fs [bytes_in_word_def, dimword_def] >>
   rveq >>
   gs [mem_call_ffi_def, ffi_call_ffi_def])
QED

Theorem evaluate_assign_load:
  ∀dst trgt (t :('a, time_input) panSem$state) res t' adr tm w.
    evaluate (Assign dst (Load One (Var trgt)),t) = (res,t') ∧
    FLOOKUP t.locals trgt = SOME (ValWord adr) ∧
    FLOOKUP t.locals dst = SOME (ValWord tm) ∧
    t.memory adr = Word w ∧
    adr ∈ t.memaddrs ⇒
      res = NONE ∧
      t' = t with locals :=
           t.locals |+
            (dst, ValWord w)
Proof
  rpt gen_tac >>
  strip_tac >>
  gs [evaluate_def, eval_def] >>
  gs [mem_load_def] >>
  gs [is_valid_value_def, shape_of_def]
QED


Theorem evaluate_assign_load_next_address:
  ∀dst trgt (t :('a, time_input) panSem$state) res t' adr w.
    evaluate (Assign dst
              (Load One (Op Add [Var trgt ; Const bytes_in_word])),t) = (res,t') ∧
    FLOOKUP t.locals trgt = SOME (ValWord adr) ∧
    (∃tm. FLOOKUP t.locals dst = SOME (ValWord tm)) ∧
    t.memory (adr + bytes_in_word) = Word w ∧
    adr + bytes_in_word ∈ t.memaddrs ⇒
      res = NONE ∧
      t' = t with locals :=
           t.locals |+
            (dst, ValWord w)
Proof
  rpt gen_tac >>
  strip_tac >>
  gs [evaluate_def, eval_def, OPT_MMAP_def] >>
  gs [mem_load_def, wordLangTheory.word_op_def] >>
  gs [is_valid_value_def, shape_of_def]
QED


Theorem evaluate_assign_compare_next_address:
  ∀dst trgt (t :('a, time_input) panSem$state) res t' adr n.
    evaluate (Assign dst
              (Cmp Equal
               (Load One (Op Add [Var trgt ; Const bytes_in_word]))
               (Const n)),t) = (res,t') ∧
    FLOOKUP t.locals trgt = SOME (ValWord adr) ∧
    (∃tm. FLOOKUP t.locals dst = SOME (ValWord tm)) ∧
    t.memory (adr + bytes_in_word) = Word n ∧
    adr + bytes_in_word ∈ t.memaddrs ⇒
      res = NONE ∧
      t' = t with locals :=
           t.locals |+
            (dst, ValWord 1w)
Proof
  rpt gen_tac >>
  strip_tac >>
  gs [evaluate_def, eval_def, OPT_MMAP_def] >>
  gs [mem_load_def, wordLangTheory.word_op_def] >>
  gs [is_valid_value_def, shape_of_def] >>
  fs [asmTheory.word_cmp_def]
QED


Theorem evaluate_assign_compare_next_address_uneq:
  ∀dst trgt (t :('a, time_input) panSem$state) res t' adr n n'.
    evaluate (Assign dst
              (Cmp Equal
               (Load One (Op Add [Var trgt ; Const bytes_in_word]))
               (Const n)),t) = (res,t') ∧
    FLOOKUP t.locals trgt = SOME (ValWord adr) ∧
    (∃tm. FLOOKUP t.locals dst = SOME (ValWord tm)) ∧
    t.memory (adr + bytes_in_word) = Word n' ∧
    n ≠ n' ∧
    adr + bytes_in_word ∈ t.memaddrs ⇒
      res = NONE ∧
      t' = t with locals :=
           t.locals |+
            (dst, ValWord 0w)
Proof
  rpt gen_tac >>
  strip_tac >>
  gs [evaluate_def, eval_def, OPT_MMAP_def] >>
  gs [mem_load_def, wordLangTheory.word_op_def] >>
  gs [is_valid_value_def, shape_of_def] >>
  fs [asmTheory.word_cmp_def]
QED


Theorem evaluate_if_compare_sys_time:
  ∀v m n t res t'.
    evaluate
    (If (Cmp Equal (Var v) (Const (n2w m)))
     (Return (Const 0w)) (Skip:'a panLang$prog),t) = (res,t') ∧
    FLOOKUP t.locals v = SOME (ValWord (n2w n)) ∧
    n < m ∧
    n < dimword (:α) ∧ m < dimword (:α) ⇒
    res = NONE ∧
    t' = t
Proof
  rpt gen_tac >>
  strip_tac >>
  gs [evaluate_def, eval_def, asmTheory.word_cmp_def] >>
  every_case_tac >> gs [eval_def, evaluate_def] >>
  every_case_tac >> gs [shape_of_def, panLangTheory.size_of_shape_def]
QED


Theorem evaluate_if_compare_sys_time1:
  ∀v m n t res t'.
    evaluate
    (If (Cmp Equal (Var v) (Const (n2w m)))
     (Return (Const 0w)) (Skip:'a panLang$prog),t) = (res,t') ∧
    FLOOKUP t.locals v = SOME (ValWord (n2w n)) ∧
    n = m ∧
    n < dimword (:α) ∧ m < dimword (:α) ⇒
    res = SOME (Return (ValWord 0w)) ∧
    t' = empty_locals t
Proof
  rpt gen_tac >>
  strip_tac >>
  gs [evaluate_def, eval_def, asmTheory.word_cmp_def] >>
  every_case_tac >> gs [eval_def, evaluate_def] >>
  every_case_tac >> gs [shape_of_def, panLangTheory.size_of_shape_def]
QED



Theorem time_seq_add_holds:
  ∀f m p.
    time_seq f m ⇒
    time_seq (λn. f (p + n)) m
Proof
  rw [time_seq_def] >>
  fs [] >>
  last_x_assum (qspec_then ‘p + n’ assume_tac) >>
  fs [ADD_SUC]
QED

Theorem byte_aligned_ba_step:
  ∀ba.
  good_dimindex (:'a) ∧ byte_align (ba:'a word) = ba ⇒
  byte_align (ba + bytes_in_word)
              = ba + bytes_in_word
Proof
  rw[good_dimindex_def]>>
  gs [byte_align_def] >>
  gs[Once (GSYM aligned_def)]>>
  drule align_add_aligned_gen>>
  rw[]>>
  first_x_assum (qspec_then ‘bytes_in_word’ assume_tac)>>
  gs[]>>
  EVAL_TAC>>
  gs [dimword_def, fcp_n2w] >>
  EVAL_TAC
QED

Theorem byte_aligned_ba_rounded:
  ∀ba x.
  good_dimindex (:'a) ∧ byte_align (ba:'a word) = ba ∧
  w2n x < w2n (bytes_in_word:'a word) ⇒
  byte_align (ba + x:'a word) = ba
Proof
  rw[good_dimindex_def, bytes_in_word_def]>>gs[dimword_def]>>
  gs [byte_align_def] >>
  gs[Once (GSYM aligned_def)]>>
  drule align_add_aligned_gen>>
  rw[]>>
  first_assum (qspec_then ‘x’ assume_tac)>>
  fs[lt_align_eq_0]
QED

Theorem read_bytearray_bytes_in_word:
  ∀m adrs be ba.
    good_dimindex (:'a) ∧ byte_align (ba:'a word) = ba ∧
    ba ∈ adrs ∧ (∃w. m ba = Word w) ⇒
    ∃bytes.
      read_bytearray (ba:'a word) (w2n (bytes_in_word:'a word))
                     (mem_load_byte m adrs be) = SOME bytes
Proof
  rw[]>>
  drule_then assume_tac byte_aligned_ba_rounded>>
  first_x_assum (qspec_then ‘ba’ assume_tac)>>
  gs[GSYM PULL_FORALL]>>
  fs[good_dimindex_def, bytes_in_word_def] >> rw[] >>gs[dimword_def]>>
  ‘8 = SUC (SUC (SUC (SUC 4)))’ by simp[]>>
  ‘4 = SUC (SUC (SUC (SUC 0)))’ by simp[]>>
  asm_rewrite_tac[GSYM ADD_SUC]>>
  rewrite_tac[read_bytearray_def]>>
  fs[mem_load_byte_def]>>
  gs[dimword_def]
QED

Theorem read_bytearray_prepend:
  ∀m adrs be ba sz.
    good_dimindex (:'a) ∧
    byte_align (ba:'a word) = ba ∧
    ba ∈ adrs ∧ (∃w. m ba = Word w) ∧
    (∃bs. read_bytearray (ba + bytes_in_word:'a word) sz
                         (mem_load_byte m adrs be) = SOME bs) ⇒
    ∃bytes.
      read_bytearray (ba:'a word) (sz + w2n (bytes_in_word:'a word))
                     (mem_load_byte m adrs be) = SOME bytes
Proof
  rw[]>>
  drule_then assume_tac byte_aligned_ba_rounded>>
  first_x_assum (qspec_then ‘ba’ assume_tac)>>
  gs[GSYM PULL_FORALL]>>
  fs[good_dimindex_def, bytes_in_word_def] >> rw[] >>gs[dimword_def]>>
  ‘8 = SUC (SUC (SUC (SUC 4)))’ by simp[]>>
  ‘4 = SUC (SUC (SUC (SUC 0)))’ by simp[]>>
  asm_rewrite_tac[GSYM ADD_SUC]>>
  rewrite_tac[read_bytearray_def]>>
  fs[mem_load_byte_def]>>
  gs[dimword_def]
QED

(* good be more generic, but its a trivial theorem *)
Theorem read_bytearray_some_bytes_for_ffi:
  ∀m adrs be ba.
    good_dimindex (:'a) ∧
    ba ∈ adrs ∧
    bytes_in_word + ba ∈ adrs ∧ byte_align ba = ba ∧
    (∃w. m ba = Word w) ∧
    (∃w. m (bytes_in_word + ba) = Word w) ⇒
    ∃bytes.
      read_bytearray (ba:'a word) (w2n (ffiBufferSize:'a word))
                     (mem_load_byte m adrs be) = SOME bytes
Proof
  rw[]>>
  ‘good_dimindex (:'a) ⇒
   w2n (ffiBufferSize:'a word) = w2n (bytes_in_word:'a word) +
                                 w2n (bytes_in_word:'a word)’
    by (gs[ffiBufferSize_def, good_dimindex_def, bytes_in_word_def]>>
        rw[]>>gs[dimword_def])>>
  first_x_assum (drule_then assume_tac)>>
  asm_rewrite_tac[]>>
  irule read_bytearray_prepend>>
  rw[read_bytearray_bytes_in_word, byte_aligned_ba_step]
QED

Theorem ffi_abs_mono:
  ∀j i (f:num -> num).
    i < j ∧
    (∀n.
       ∃d.
         f (SUC n) =
         d + f n) ⇒
    f i ≤ f j
Proof
  Induct >>
  rw [] >>
  fs [] >>
  cases_on ‘i < j’
  >- (
    last_x_assum drule >>
    disch_then (qspec_then ‘f’ mp_tac) >>
    impl_tac >- gs [] >>
    strip_tac >>
    last_x_assum (qspec_then ‘j’ mp_tac) >>
    strip_tac >> gs []) >>
  cases_on ‘i = j’
  >- (
    rveq >>
    gs [] >>
    first_x_assum (qspec_then ‘i’ assume_tac) >>
    gs []) >>
  gs []
QED



Theorem sum_mod_eq_lt_eq:
  (a + b) MOD k = (a + c) MOD (k:num) ∧
  a < k ∧
  b < k ∧
  c < k ⇒
  b = c
Proof
  once_rewrite_tac [ADD_COMM] >>
  reverse (Cases_on ‘0 < k’)
  >- fs [] >>
  drule ADD_MOD >>
  disch_then (fs o single) >>
  rw [] >> fs []
QED



(* wakeup rel need to be updated *)
Theorem step_delay_loop:
  !cycles prog d m n s s' (t:('a,time_input) panSem$state) ck0 ist.
    step prog (LDelay d) m n s s' ∧
    m = dimword (:α) - 1 ∧
    n = FST (t.ffi.ffi_state 0) ∧
    state_rel (clksOf prog) (out_signals prog) s t ∧
    code_installed t.code prog ∧
    delay_rep d t.ffi.ffi_state cycles ∧
    wakeup_shape t.locals s.waitTime ist ∧
    wakeup_rel t.locals s.waitTime ist t.ffi.ffi_state cycles ∧
    mem_read_ffi_results (:α) t.ffi.ffi_state cycles ∧
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «event» =  SOME (ValWord 0w) ∧
    good_dimindex (:'a) ==>
    ?ck t'.
      (∀ck_extra.
         evaluate (wait_input_time_limit, t with clock := t.clock + ck + ck_extra) =
         evaluate (wait_input_time_limit, t' with clock := t'.clock + ck_extra + ck0)) ∧
      code_installed t'.code prog ∧
      state_rel (clksOf prog) (out_signals prog) s' t' ∧
      t'.ffi.ffi_state = nexts_ffi cycles t.ffi.ffi_state ∧
      t'.ffi.oracle = t.ffi.oracle ∧
      t'.code = t.code ∧
      t'.be = t.be ∧ t'.base_addr = t.base_addr ∧
      t'.eshapes = t.eshapes ∧
      FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt» ∧
      FLOOKUP t'.locals «waitSet» = FLOOKUP t.locals «waitSet» ∧
      FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
      FLOOKUP t'.locals «event» =  SOME (ValWord 0w) ∧
      FLOOKUP t'.locals «taskRet» = FLOOKUP t.locals «taskRet» ∧
      FLOOKUP t'.locals «sysTime»  =
      SOME (ValWord (n2w (FST (t.ffi.ffi_state cycles)))) ∧
      wait_time_locals1 (:α) t'.locals s'.waitTime
                       ist (FST (t.ffi.ffi_state cycles)) ∧
      (t.ffi.io_events ≠ [] ∧
       EL 0 (io_event_dest (:α) t.be (LAST t.ffi.io_events)) = FST (t.ffi.ffi_state 0) ⇒
       delay_io_events_rel t t' cycles ∧
       obs_ios_are_label_delay d t t')
Proof
  Induct_on ‘cycles’ >>
  fs []
  >- (
    rw [] >>
    fs [delay_rep_def] >>
    ‘d = 0’ by fs [] >>
    fs [] >>
    pop_assum kall_tac >>
    fs [step_cases] >>
    fs [delay_clocks_def, mkState_def] >>
    rveq >> rgs [] >>
    fs [fmap_to_alist_eq_fm] >>
    qexists_tac ‘ck0’ >> fs [] >>
    qexists_tac ‘t’ >> fs [] >>
    rgs [state_rel_def, nexts_ffi_def, GSYM ETA_AX] >>
    pairarg_tac >> rgs [] >>
    rgs [delay_io_events_rel_def, mk_ti_events_def, gen_ffi_states_def,
        io_events_eq_ffi_seq_def, from_io_events_def, io_events_dest_def,
        io_event_dest_def, DROP_LENGTH_NIL] >>
    rgs [obs_ios_are_label_delay_def, DROP_LENGTH_NIL,
        decode_io_events_def, delay_ios_mono_def] >>
    rgs [wait_time_locals1_def]
    >- (
      rgs [wakeup_shape_def] >>
      qexists_tac ‘wt'’ >>
      rgs []) >>
    rgs [wakeup_shape_def] >>
    qexists_tac ‘wt'’ >>
    rgs [] >>
    strip_tac >>
    rgs [wakeup_rel_def]) >>
  rw [] >>
  ‘∃sd. sd ≤ d ∧
        delay_rep sd t.ffi.ffi_state cycles’ by (
    fs [delay_rep_def] >>
    imp_res_tac state_rel_imp_time_seq_ffi >>
    ‘FST (t.ffi.ffi_state 0) ≤ FST (t.ffi.ffi_state cycles)’ by (
      match_mp_tac time_seq_mono >>
      qexists_tac ‘(dimword (:α))’ >>
      fs []) >>
    fs [time_seq_def] >>
    first_x_assum (qspec_then ‘cycles’ mp_tac) >>
    first_x_assum (qspec_then ‘cycles’ mp_tac) >>
    strip_tac >> strip_tac >>
    rgs [] >>
    qexists_tac ‘d - d'’ >>
    rgs [] >>
    qexists_tac ‘st’ >> fs []) >>
  qpat_x_assum ‘step _ _ _ _ _ _’ mp_tac >>
  rewrite_tac [step_cases] >>
  strip_tac >>
  fs [] >> rveq
  >- (
    ‘step prog (LDelay sd) (dimword (:α) - 1) (FST (t.ffi.ffi_state 0)) s
     (mkState (delay_clocks s.clocks sd) s.location NONE NONE)’ by (
      rgs [mkState_def] >>
      fs [step_cases, mkState_def, max_clocks_def] >>
      rgs [delay_clocks_def] >>
      rw [] >>
      rgs [flookup_update_list_some] >>
      drule ALOOKUP_MEM >>
      strip_tac >>
      rgs [GSYM MAP_REVERSE] >>
      rgs [MEM_MAP] >>
      cases_on ‘y’ >> rgs [] >>
      rveq >> rgs [] >>
      first_x_assum (qspecl_then [‘ck’,
                                  ‘r + (d + FST (t.ffi.ffi_state 0))’] mp_tac) >>
      impl_tac
      >- (
        match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
        rgs [] >>
        conj_tac
        >- (
        rgs [MAP_REVERSE] >>
        ‘MAP FST (MAP (λ(x,y). (x,d + (y + FST (t.ffi.ffi_state 0))))
                  (fmap_to_alist s.clocks)) =
         MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
        rgs []) >>
        rgs [MEM_MAP] >>
        qexists_tac ‘(ck,r)’ >>
        rgs []) >>
      strip_tac >>
      rgs []) >>
    last_x_assum drule >>
    (* ck0 *)
    disch_then (qspecl_then [‘ck0 + 1’, ‘ist’] mp_tac) >>
    impl_tac
    >- (
      rgs [mkState_def, wakeup_rel_def, mem_read_ffi_results_def] >>
      rpt gen_tac >>
      strip_tac >>
      last_x_assum (qspecl_then [‘i’,‘t'’, ‘t''’] mp_tac) >>
      rgs []) >>
    strip_tac >> fs [] >>
    ‘(mkState (delay_clocks s.clocks d) s.location NONE NONE).ioAction =
     NONE’ by fs [mkState_def] >>
    fs [] >>
    pop_assum kall_tac >>
    ‘(mkState (delay_clocks s.clocks sd) s.location NONE NONE).ioAction =
     NONE’ by fs [mkState_def] >>
    fs [] >>
    pop_assum kall_tac >>
    qexists_tac ‘ck’ >>
    fs [] >>
    qpat_x_assum ‘∀ck_extra. _’ kall_tac >>
    drule state_rel_imp_mem_config >>
    rewrite_tac [Once mem_config_def] >>
    strip_tac >>
    fs [] >>
    ‘∃bytes.
       read_bytearray t'.base_addr (w2n (ffiBufferSize:'a word))
                      (mem_load_byte t'.memory t'.memaddrs t'.be) = SOME bytes’ by (
      match_mp_tac read_bytearray_some_bytes_for_ffi >>
      rgs [state_rel_def]) >>
    gvs [] >>
    qabbrev_tac
    ‘new_t:('a,time_input) panSem$state =
           t' with
              <|locals :=
                t'.locals |+
                  («sysTime» ,
                   ValWord (n2w (FST (nexts_ffi cycles t.ffi.ffi_state 1)))) |+
                  («event» ,
                   ValWord (n2w (SND (nexts_ffi cycles t.ffi.ffi_state 1)))) |+
                  («isInput» ,ValWord 1w);
                memory :=
                mem_call_ffi (:α) t'.memory t'.memaddrs t.be t.base_addr
                             (nexts_ffi cycles t.ffi.ffi_state);
                ffi := ffi_call_ffi (:α) t.be t'.ffi bytes|>’ >>
    qexists_tac ‘new_t’ >>
    fs [PULL_FORALL] >>
    gen_tac >> rgs [] >>
    fs [wait_input_time_limit_def] >>
    rewrite_tac [Once evaluate_def] >>
    drule step_delay_eval_wait_not_zero >>
    impl_tac
    >- (
      rgs [state_rel_def, mkState_def, equivs_def, time_vars_def, active_low_def] >>
      pairarg_tac >> rgs []) >>
    strip_tac >>
    rgs [eval_upd_clock_eq] >>
    rgs [dec_clock_def] >>
    (* evaluating the function *)
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    ‘state_rel (clksOf prog) (out_signals prog)
     (mkState (delay_clocks s.clocks sd) s.location NONE NONE)
     (t' with clock := ck_extra + t'.clock)’ by rgs [state_rel_def] >>
    qpat_x_assum ‘state_rel _ _ _ t'’ kall_tac >>
    rewrite_tac [Once check_input_time_def] >>
    fs [panLangTheory.nested_seq_def] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    drule evaluate_ext_call >>
    disch_then (qspecl_then [‘MAP explode (out_signals prog)’,‘bytes’] mp_tac) >>
    impl_tac
    >- (
      rgs [state_rel_def] >>
      pairarg_tac >> rgs []) >>
    strip_tac >> gvs [] >>
    drule state_rel_imp_ffi_vars >>
    strip_tac >>
    pop_assum mp_tac >>
    rewrite_tac [Once ffi_vars_def] >>
    strip_tac >>
    drule state_rel_imp_systime_defined >>
    strip_tac >>
    (* reading systime *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
    ‘nt.memory t'.base_addr = Word (n2w (FST(t'.ffi.ffi_state 1)))’ by (
      fs [Abbr ‘nt’] >>
      qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
      rgs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
      last_x_assum
      (qspecl_then
       [‘cycles’,
        ‘t' with clock := ck0 + ck_extra + t'.clock’,
        ‘ft’] mp_tac)>>
      impl_tac
      >- rgs [Abbr ‘ft’] >>
      strip_tac >>
      rgs [Abbr ‘ft’]) >>
    drule evaluate_assign_load >>
    rgs [] >>
    disch_then (qspecl_then
                [‘t'.base_addr’, ‘tm’,
                 ‘n2w (FST (t'.ffi.ffi_state 1))’] mp_tac) >>
    impl_tac
    >- (
      rgs [Abbr ‘nt’] >>
      fs [state_rel_def]) >>
    strip_tac >> fs [] >>
    gvs [] >>
    (* reading input to the variable event *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «event» _, nnt)’ >>
    ‘nnt.memory (t'.base_addr +  bytes_in_word) =
     Word (n2w (SND(t'.ffi.ffi_state 1)))’ by (
      fs [Abbr ‘nnt’, Abbr ‘nt’] >>
      qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
      rgs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
      last_x_assum
      (qspecl_then
       [‘cycles’,
        ‘t' with clock := ck0 + ck_extra + t'.clock’,
        ‘ft’] mp_tac)>>
      impl_tac
      >- rgs [Abbr ‘ft’] >>
      strip_tac >>
      rgs [Abbr ‘ft’]) >>
    rgs [] >>
    drule evaluate_assign_load_next_address >>
    rgs [] >>
    disch_then (qspecl_then
                [‘t.base_addr’,
                 ‘n2w (SND (nexts_ffi cycles t.ffi.ffi_state 1))’] mp_tac) >>
    impl_tac
    >- (
      rgs [Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
      rgs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
      rgs [delay_rep_def, nexts_ffi_def]) >>
    strip_tac >> gvs [] >>
    (* isInput *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «isInput» _, nnnt)’ >>
    ‘nnnt.memory (t'.base_addr +  bytes_in_word) =
     Word (n2w (SND(t'.ffi.ffi_state 1)))’ by fs [Abbr ‘nnnt’] >>
    rgs [] >>
    ‘nnnt.memory (t'.base_addr +  bytes_in_word) = Word 0w’ by (
      rgs [delay_rep_def] >>
      fs [nexts_ffi_def]) >>
      fs [] >>
    drule evaluate_assign_compare_next_address >>
    rgs [] >>
    disch_then (qspecl_then [‘t.base_addr’] mp_tac) >>
    impl_tac
    >- (
      rgs [Abbr ‘nnnt’, Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
      rgs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
      rgs [delay_rep_def, nexts_ffi_def]) >>
    strip_tac >> gvs [] >>
    (* If statement *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    drule evaluate_if_compare_sys_time >>
    disch_then (qspec_then ‘FST (nexts_ffi cycles t.ffi.ffi_state 1)’ mp_tac) >>
    impl_tac
    >- (
      unabbrev_all_tac >>
      rgs [FLOOKUP_UPDATE, nexts_ffi_def] >>
      rgs [delay_rep_def, ADD1]) >>
    strip_tac >> rveq >> rgs [] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    strip_tac >> fs [] >>
    rveq >> rgs [] >>
    unabbrev_all_tac >>
    rgs [] >> gvs [] >>
    reverse conj_tac
    >- (
      fs [ffi_call_ffi_def] >>
      fs [nexts_ffi_def, next_ffi_def, FLOOKUP_UPDATE] >>
      fs [ADD1] >>
      conj_asm1_tac
      >- (
        rgs [wait_time_locals1_def, FLOOKUP_UPDATE, mkState_def] >>
        qexists_tac ‘wt’ >> rgs []) >>
      strip_tac >> rgs [] >>
      conj_asm1_tac
      >- (
        fs [delay_io_events_rel_def] >>
        conj_asm1_tac
        >- (
          qexists_tac ‘bytess ++ [bytes]’ >>
          rgs [] >>
          drule read_bytearray_LENGTH >>
          strip_tac >>
          conj_asm1_tac
          >- (
            rgs [ffiBufferSize_def, bytes_in_word_def] >>
            rgs [good_dimindex_def, dimword_def]) >>
          rgs [mk_ti_events_def] >>
          ‘gen_ffi_states t.ffi.ffi_state (LENGTH bytess + 1) =
           gen_ffi_states t.ffi.ffi_state (LENGTH bytess) ++
                          [(λn. t.ffi.ffi_state (n + LENGTH bytess))]’ by (
            fs [gen_ffi_states_def] >>
            rgs [GSYM ADD1, GENLIST]) >>
          rgs [] >>
          ‘LENGTH [bytes] = LENGTH [(λn. t.ffi.ffi_state (n + LENGTH bytess))] ∧
           LENGTH bytess = LENGTH (gen_ffi_states t.ffi.ffi_state (LENGTH bytess))’ by
            rgs [gen_ffi_states_def] >>
          drule ZIP_APPEND >>
          disch_then (qspecl_then [‘[bytes]’,
                                   ‘[(λn. t.ffi.ffi_state (n + LENGTH bytess))]’] mp_tac) >>
          impl_tac
          >- rgs [] >>
          strip_tac >>
          pop_assum (assume_tac o GSYM) >>
          rgs [mk_ti_event_def, time_input_def]) >>
        (* proving io_events rel *)
        rgs [from_io_events_def] >>
        rewrite_tac [GSYM APPEND_ASSOC] >>
        rgs [DROP_LENGTH_APPEND] >>
        rgs [mk_ti_events_def, io_events_dest_def] >>
        rgs [MAP_MAP_o] >>
        rgs [io_events_eq_ffi_seq_def] >>
        rgs [gen_ffi_states_def] >>
        rgs [EVERY_MEM] >>
        rw [] >> rgs []
        >- (
          rgs [MEM_MAP] >>
          drule MEM_ZIP2 >>
          strip_tac >> rgs [] >>
          rgs [mk_ti_event_def, io_event_dest_def] >>
          qmatch_goalsub_abbrev_tac ‘ZIP (nn, mm)’ >>
          ‘LENGTH nn = LENGTH mm’ by (
            fs [Abbr ‘nn’, Abbr ‘mm’] >>
            first_x_assum (qspec_then ‘EL n bytess'’ mp_tac) >>
            impl_tac
            >- (
              rgs [MEM_EL] >>
              metis_tac []) >>
            strip_tac >> rgs [] >>
            rgs [time_input_def, length_get_bytes] >>
            rgs [good_dimindex_def]) >>
          ‘MAP SND (ZIP (nn,mm)) = mm’ by (
            drule MAP_ZIP >>
            rgs []) >>
          rgs [] >>
          rgs [words_of_bytes_def] >>
          ‘8 ≤ dimindex (:α)’ by rgs [good_dimindex_def] >>
          drule LENGTH_words_of_bytes >>
          disch_then (qspecl_then [‘t.be’, ‘mm’] mp_tac) >>
          strip_tac >> rgs [] >>
          rgs [Abbr ‘mm’, time_input_def, length_get_bytes, bytes_in_word_def,
              good_dimindex_def, dimword_def])
        >- (
          qpat_x_assum ‘MAP _ _ ++ _ = _’ (assume_tac o GSYM) >>
          rgs [GSYM MAP_MAP_o] >>
          cases_on ‘i < LENGTH bytess’
          >- (
            last_x_assum (qspec_then ‘i’ mp_tac) >>
            impl_tac >- rgs [] >>
            strip_tac >>
            rgs [EL_APPEND_EQN]) >>
          rgs [EL_APPEND_EQN] >>
          ‘i − LENGTH bytess = 0’ by rgs [] >>
          simp [] >>
          rgs [io_event_dest_def] >>
          qmatch_goalsub_abbrev_tac ‘ZIP (nn, mm)’ >>
          ‘LENGTH nn = LENGTH mm’ by (
            fs [Abbr ‘nn’, Abbr ‘mm’] >>
            drule read_bytearray_LENGTH >>
            strip_tac >>
            rgs [length_get_bytes, ffiBufferSize_def,
                good_dimindex_def, bytes_in_word_def, dimword_def]) >>
          ‘MAP SND (ZIP (nn,mm)) = mm’ by (
            drule MAP_ZIP >>
            rgs []) >>
          rgs [Abbr ‘mm’] >>
          qmatch_goalsub_abbrev_tac ‘get_bytes t.be aa ++ get_bytes t.be bb’ >>
          ‘words_of_bytes t.be (get_bytes t.be aa ++ get_bytes t.be bb) =
           [aa;bb]’ by (
            match_mp_tac words_of_bytes_get_bytes >>
            rgs []) >>
          rgs [Abbr ‘aa’, Abbr ‘bb’] >>
          rgs [delay_rep_def] >>
          cases_on ‘t.ffi.ffi_state (i+1)’ >> rgs [] >>
          last_x_assum (qspec_then ‘i + 1’ mp_tac) >>
          rgs [] >>
          strip_tac >>
          qpat_x_assum ‘_ = d + FST (t.ffi.ffi_state 0)’ (mp_tac o GSYM) >>
          rgs [] >>
          strip_tac >>
          ‘LENGTH bytess = i’ by rgs [] >>
          simp []) >>
        rgs [decode_io_events_def] >>
        rgs [MAP_MAP_o] >>
        qmatch_goalsub_abbrev_tac ‘EL n (MAP f l)’ >>
        ‘EL n (MAP f l) = f (EL n l)’ by (
          match_mp_tac EL_MAP >>
          rgs [Abbr ‘f’, Abbr ‘l’]) >>
        rgs [Abbr ‘f’, Abbr ‘l’] >>
        qmatch_goalsub_abbrev_tac ‘ZIP (l1, l2)’ >>
        ‘EL n (ZIP (l1,l2)) = (EL n l1,EL n l2)’ by (
          match_mp_tac EL_ZIP >>
          rgs [Abbr ‘l1’, Abbr ‘l2’]) >>
        rgs [Abbr ‘l1’, Abbr ‘l2’] >>
        qmatch_goalsub_abbrev_tac ‘EL n (MAP f l)’ >>
        ‘EL n (MAP f l) = f (EL n l)’ by (
          match_mp_tac EL_MAP >>
          rgs [Abbr ‘f’, Abbr ‘l’]) >>
        rgs [Abbr ‘f’, Abbr ‘l’] >>
        rgs [mk_ti_event_def, decode_io_event_def] >>
        qmatch_goalsub_abbrev_tac ‘EL 1 nio’ >>
        ‘EL 1 nio = 0’ by (
          rgs [Abbr ‘nio’, io_event_dest_def] >>
          qmatch_goalsub_abbrev_tac ‘ZIP (nn, mm)’ >>
          ‘LENGTH nn = LENGTH mm’ by (
            fs [Abbr ‘nn’, Abbr ‘mm’] >>
            rgs [time_input_def, length_get_bytes] >>
            first_x_assum (qspec_then ‘EL n bytess'’ mp_tac) >>
            impl_tac >- metis_tac [MEM_EL] >>
            rgs [good_dimindex_def]) >>
          ‘MAP SND (ZIP (nn,mm)) = mm’ by (
            drule MAP_ZIP >>
            rgs []) >>
          rgs [Abbr ‘nn’, Abbr ‘mm’] >>
          rgs [time_input_def] >>
          qmatch_goalsub_abbrev_tac ‘get_bytes t.be aa ++ get_bytes t.be bb’ >>
          ‘words_of_bytes t.be (get_bytes t.be aa ++ get_bytes t.be bb) =
           [aa;bb]’ by (
            match_mp_tac words_of_bytes_get_bytes >>
            rgs []) >>
          rgs [Abbr ‘aa’, Abbr ‘bb’] >>
          rgs [delay_rep_def]) >>
        rgs [Abbr ‘nio’] >>
        rgs [io_event_dest_def] >>
        qmatch_goalsub_abbrev_tac ‘ZIP (nn, mm)’ >>
        ‘LENGTH nn = LENGTH mm’ by (
          fs [Abbr ‘nn’, Abbr ‘mm’] >>
          rgs [time_input_def, length_get_bytes] >>
          first_x_assum (qspec_then ‘EL n bytess'’ mp_tac) >>
          impl_tac >- metis_tac [MEM_EL] >>
          rgs [good_dimindex_def]) >>
        ‘MAP SND (ZIP (nn,mm)) = mm’ by (
          drule MAP_ZIP >>
          rgs []) >>
        rgs [Abbr ‘nn’, Abbr ‘mm’] >>
        rgs [time_input_def, length_get_bytes] >>
        qmatch_goalsub_abbrev_tac ‘get_bytes t.be aa ++ get_bytes t.be bb’ >>
        ‘words_of_bytes t.be (get_bytes t.be aa ++ get_bytes t.be bb) =
         [aa;bb]’ by (
          match_mp_tac words_of_bytes_get_bytes >>
          rgs []) >>
        rgs [Abbr ‘aa’, Abbr ‘bb’] >>
        last_x_assum assume_tac >>
        rgs [state_rel_def] >>
        pairarg_tac >> rgs [] >>
        rgs [time_seq_def]) >>
      rgs [obs_ios_are_label_delay_def] >>
      reverse conj_tac
      >- (
        pop_assum mp_tac >>
        once_rewrite_tac [delay_io_events_rel_def] >>
        fs [] >>
        strip_tac >>
        qmatch_goalsub_abbrev_tac ‘EL n ios’ >>
        strip_tac >>
        first_x_assum (qspec_then ‘n’ mp_tac) >>
        impl_tac
        >- (
          rgs [Abbr ‘ios’, Abbr ‘n’] >>
          rewrite_tac [GSYM APPEND_ASSOC] >>
          rgs [DROP_LENGTH_APPEND] >>
          rgs [decode_io_events_def, mk_ti_events_def, gen_ffi_states_def]) >>
        rgs [] >>
        strip_tac >>
        rgs [to_delay_def] >>
        rgs [Abbr ‘n’, Abbr ‘ios’, DROP_LENGTH_APPEND] >>
        rgs [decode_io_events_def, mk_ti_events_def, gen_ffi_states_def] >>
        rgs [delay_rep_def]) >>
      pop_assum mp_tac >>
      once_rewrite_tac [delay_io_events_rel_def] >>
      fs [] >>
      strip_tac >>
      simp [delay_ios_mono_def] >>
      rw [] >>
      last_x_assum assume_tac >>
      rgs [state_rel_def] >>
      pairarg_tac >> rgs [] >>
      rgs [time_seq_def] >>
      ‘(λx. FST (t.ffi.ffi_state x)) (i + 1) ≤ (λx. FST (t.ffi.ffi_state x)) (j + 1)’ by (
        match_mp_tac ffi_abs_mono >>
        rgs []) >>
      rgs []) >>
    (* proving state rel *)
    rgs [state_rel_def, mkState_def] >>
    conj_tac
    (* equivs *)
    >- rgs [equivs_def, FLOOKUP_UPDATE, active_low_def] >>
    conj_tac
    >- rgs [ffi_vars_def, FLOOKUP_UPDATE] >>
    conj_tac
    >- rgs [time_vars_def, FLOOKUP_UPDATE] >>
    conj_tac
    >- rgs [mem_config_def, mem_call_ffi_def] >>
    conj_tac
    >- (
      (* clock_bound *)
      qpat_x_assum ‘defined_clocks s.clocks _’ assume_tac >>
      rgs [defined_clocks_def] >>
      fs [EVERY_MEM] >>
      rw [] >>
      first_x_assum drule >>
      strip_tac >>
      fs [] >>
      fs [delay_clocks_def] >>
      qexists_tac ‘d+n’ >>
      rgs [] >>
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(ck,n)’ >>
      fs []) >>
    pairarg_tac >> rgs [] >>
    conj_tac
    >- (
      fs [ffi_call_ffi_def, build_ffi_def] >>
      fs [ffiTheory.ffi_state_component_equality] >>
      last_x_assum assume_tac >>
      pairarg_tac >>
      fs [] >>
      pairarg_tac >>
      fs []) >>
    conj_tac
    >- (
      (* input_time_rel *)
      rgs [input_time_rel_def] >>
      rw [] >>
      rgs [input_time_eq_def, ffi_call_ffi_def, next_ffi_def, nexts_ffi_def,
          has_input_def] >>
      strip_tac >>
      pairarg_tac >> rgs [] >>
      first_x_assum (qspec_then ‘n+1’ mp_tac) >>
      impl_tac >- rgs [] >>
      rgs []) >>
    conj_tac
    >- (
      (* time_seq holds *)
      rgs [ffi_call_ffi_def,
          nexts_ffi_def, next_ffi_def] >>
      qpat_x_assum ‘_ (t.ffi.ffi_state 0)’ mp_tac >>
      pairarg_tac >> rgs [] >>
      strip_tac >>
      drule time_seq_add_holds >>
      disch_then (qspec_then ‘cycles + 1’ mp_tac) >>
      fs [])  >>
    (* clocks_rel *)
    qpat_x_assum ‘_ (nexts_ffi _ _ _)’ assume_tac >>
    rgs [clocks_rel_def, FLOOKUP_UPDATE,
        nexts_ffi_def, ffi_call_ffi_def, next_ffi_def, time_seq_def] >>
    pairarg_tac >> rgs [] >> rveq >> rgs [] >>
    qexists_tac ‘ns’ >>
    fs [] >>
    fs [clkvals_rel_def] >>
    conj_tac
    >- (
      fs [MAP_EQ_EVERY2] >>
      fs [LIST_REL_EL_EQN] >>
      rw [] >>
      pairarg_tac >> fs [] >>
      last_x_assum drule >>
      fs [] >>
      strip_tac >>
      (* shortcut *)
      ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
        drule EL_ZIP >>
        disch_then (qspec_then ‘n’ mp_tac) >>
        rgs [] >>
        strip_tac >>
        rgs [defined_clocks_def] >>
        fs [EVERY_MEM] >>
        fs [MEM_EL] >>
        last_x_assum (qspec_then ‘x’ mp_tac) >>
        fs [] >>
        impl_tac >- metis_tac [] >>
        rgs [FDOM_FLOOKUP]) >>
      fs [delay_clocks_def] >>
      ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
       x = SOME (d + xn)’ by (
        match_mp_tac mem_to_flookup >>
        ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
         MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
        fs [ALL_DISTINCT_fmap_to_alist_keys] >>
        fs [MEM_MAP] >>
        qexists_tac ‘(x,xn)’ >>
        fs []) >>
      fs [] >>
      ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
       x = SOME (sd + xn)’ by (
        match_mp_tac mem_to_flookup >>
        ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
         MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
        fs [ALL_DISTINCT_fmap_to_alist_keys] >>
        fs [MEM_MAP] >>
        qexists_tac ‘(x,xn)’ >>
        fs []) >>
      fs [] >>
      fs [ffi_call_ffi_def, next_ffi_def] >>
      qpat_x_assum ‘delay_rep d _ _’ assume_tac >>
      qpat_x_assum ‘delay_rep sd _ _’ assume_tac >>
      qpat_x_assum ‘sd ≤ d’ assume_tac >>
      rgs [delay_rep_def] >>
      rgs [ADD1]) >>
    (* repetition *)
    fs [EVERY_MEM] >>
    rw [] >>
    first_x_assum (qspec_then ‘x’ assume_tac) >>
    rgs [] >>
    ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
      rgs [defined_clocks_def] >>
      rgs [EVERY_MEM]) >>
    fs [delay_clocks_def] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
     x = SOME (d + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
     x = SOME (sd + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    fs [ffi_call_ffi_def, next_ffi_def] >>
    qpat_x_assum ‘delay_rep d _ _’ assume_tac >>
    qpat_x_assum ‘delay_rep sd _ _’ assume_tac >>
    qpat_x_assum ‘sd ≤ d’ assume_tac >>
    rgs [delay_rep_def] >>
    rgs [ADD1]) >>
  ‘step prog (LDelay sd) (dimword (:α) - 1) (FST (t.ffi.ffi_state 0)) s
   (mkState (delay_clocks s.clocks sd) s.location NONE (SOME (w - sd)))’ by (
    rgs [mkState_def] >>
    fs [step_cases, mkState_def, max_clocks_def] >>
    rgs [delay_clocks_def] >>
    rw [] >>
    rgs [flookup_update_list_some] >>
    drule ALOOKUP_MEM >>
    strip_tac >>
    rgs [GSYM MAP_REVERSE] >>
    rgs [MEM_MAP] >>
    cases_on ‘y’ >> rgs [] >>
    rveq >> rgs [] >>
    first_x_assum (qspecl_then [‘ck’,
                                ‘r + (d + FST (t.ffi.ffi_state 0))’] mp_tac) >>
    impl_tac
    >- (
      match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
      rgs [] >>
      conj_tac
      >- (
        rgs [MAP_REVERSE] >>
        ‘MAP FST (MAP (λ(x,y). (x,d + (y + FST (t.ffi.ffi_state 0))))
                  (fmap_to_alist s.clocks)) =
         MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
        rgs []) >>
      rgs [MEM_MAP] >>
      qexists_tac ‘(ck,r)’ >>
      rgs []) >>
    strip_tac >>
    rgs []) >>
  last_x_assum drule >>
  (* ck0 *)
  disch_then (qspecl_then [‘ck0 + 1’, ‘ist’] mp_tac) >>
  impl_tac
  >- (
    rgs [mkState_def, wakeup_rel_def] >>
    rgs [delay_rep_def] >>
    rgs [mem_read_ffi_results_def] >>
    rpt gen_tac >>
    strip_tac >>
    last_x_assum (qspecl_then [‘i’,‘t'’, ‘t''’] mp_tac) >>
    rgs []) >>
  strip_tac >> fs [] >>
  ‘(mkState (delay_clocks s.clocks d) s.location NONE (SOME (w - d))).ioAction =
   NONE’ by fs [mkState_def] >>
  fs [] >>
  pop_assum kall_tac >>
  ‘(mkState (delay_clocks s.clocks sd) s.location NONE (SOME (w - sd))).ioAction =
   NONE’ by fs [mkState_def] >>
  fs [] >>
  pop_assum kall_tac >>
  (* cases on d < w *)
  cases_on ‘d < w’ >> rgs []
  >- (
    qexists_tac ‘ck’ >>
    fs [] >>
    qpat_x_assum ‘∀ck_extra. _’ kall_tac >>
    drule state_rel_imp_mem_config >>
    rewrite_tac [Once mem_config_def] >>
    strip_tac >>
    fs [] >>
    ‘∃bytes.
       read_bytearray t'.base_addr (w2n (ffiBufferSize:'a word))
                      (mem_load_byte t'.memory t'.memaddrs t'.be) = SOME bytes’ by (
      match_mp_tac read_bytearray_some_bytes_for_ffi >>
      rgs [state_rel_def]) >>
    gvs [] >>
    qabbrev_tac
    ‘new_t:('a,time_input) panSem$state =
           t' with
              <|locals :=
                t'.locals |+
                  («sysTime» ,
                   ValWord (n2w (FST (nexts_ffi cycles t.ffi.ffi_state 1)))) |+
                  («event» ,
                   ValWord (n2w (SND (nexts_ffi cycles t.ffi.ffi_state 1)))) |+
                  («isInput» ,ValWord 1w);
                memory :=
                mem_call_ffi (:α) t'.memory t'.memaddrs t.be t.base_addr
                             (nexts_ffi cycles t.ffi.ffi_state);
                ffi := ffi_call_ffi (:α) t.be t'.ffi bytes|>’ >>
    qexists_tac ‘new_t’ >>
    fs [PULL_FORALL] >>
    gen_tac >> rgs [] >>
    fs [wait_input_time_limit_def] >>
    rewrite_tac [Once evaluate_def] >>
    drule step_wait_delay_eval_wait_not_zero >>
    impl_tac
    >- (
      conj_tac
      >- rgs [state_rel_def, mkState_def, equivs_def, active_low_def] >>
      rgs [] >>
      rgs [wakeup_rel_def, delay_rep_def] >>
      qexists_tac ‘sd + FST (t.ffi.ffi_state 0)’ >>
      rgs [] >>
      qexists_tac ‘(ist + w) - (sd +  FST (t.ffi.ffi_state 0))’ >>
      rgs [] >>
      ‘ist + w − (sd + FST (t.ffi.ffi_state 0)) + FST (t.ffi.ffi_state 0) =
       ist + w − sd’ by (
        once_rewrite_tac [SUB_PLUS] >>
        ‘FST (t.ffi.ffi_state 0) ≤ ist + w − sd’ by (
          rgs [] >>
          first_x_assum (qspec_then ‘cycles’ mp_tac) >>
          rgs []) >>
        drule SUB_ADD >>
        rgs []) >>
      fs [] >>
      first_x_assum (qspec_then ‘cycles’ mp_tac) >>
      rgs []) >>
    strip_tac >>
    rgs [eval_upd_clock_eq] >>
    (* evaluating the function *)
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    fs [dec_clock_def] >>
    ‘state_rel (clksOf prog) (out_signals prog)
     (mkState (delay_clocks s.clocks sd) s.location NONE (SOME (w − sd)))
     (t' with clock := ck_extra + t'.clock)’ by rgs [state_rel_def] >>
    qpat_x_assum ‘state_rel _ _ _ t'’ kall_tac >>
    rewrite_tac [Once check_input_time_def] >>
    fs [panLangTheory.nested_seq_def] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    drule evaluate_ext_call >>
    disch_then (qspecl_then [‘MAP explode (out_signals prog)’,‘bytes’] mp_tac) >>
    impl_tac
    >- (
      rgs [state_rel_def] >>
      pairarg_tac >> rgs []) >>
    strip_tac >> gvs [] >>
    drule state_rel_imp_ffi_vars >>
    strip_tac >>
    pop_assum mp_tac >>
    rewrite_tac [Once ffi_vars_def] >>
    strip_tac >>
    drule state_rel_imp_systime_defined >>
    strip_tac >>
    (* reading systime *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
    ‘nt.memory t'.base_addr = Word (n2w (FST(t'.ffi.ffi_state 1)))’ by (
      fs [Abbr ‘nt’] >>
      qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
      rgs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
      last_x_assum
      (qspecl_then
       [‘cycles’,
        ‘t' with clock := ck0 + ck_extra + t'.clock’,
        ‘ft’] mp_tac)>>
      impl_tac
      >- rgs [Abbr ‘ft’] >>
      strip_tac >>
      rgs [Abbr ‘ft’]) >>
    drule evaluate_assign_load >>
    rgs [] >>
    disch_then (qspecl_then
                [‘t'.base_addr’, ‘tm’,
                 ‘n2w (FST (t'.ffi.ffi_state 1))’] mp_tac) >>
    impl_tac
    >- (
      rgs [Abbr ‘nt’] >>
      fs [state_rel_def]) >>
    strip_tac >> fs [] >>
    gvs [] >>
    (* reading input to the variable event *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «event» _, nnt)’ >>
    ‘nnt.memory (t'.base_addr +  bytes_in_word) =
     Word (n2w (SND(t'.ffi.ffi_state 1)))’ by (
      fs [Abbr ‘nnt’, Abbr ‘nt’] >>
      qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
      rgs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
      last_x_assum
      (qspecl_then
       [‘cycles’,
        ‘t' with clock := ck0 + ck_extra + t'.clock’,
        ‘ft’] mp_tac)>>
      impl_tac
      >- rgs [Abbr ‘ft’] >>
      strip_tac >>
      rgs [Abbr ‘ft’]) >>
    rgs [] >>
    drule evaluate_assign_load_next_address >>
    rgs [] >>
    disch_then (qspecl_then
                [‘t'.base_addr’,
                 ‘n2w (SND (nexts_ffi cycles t.ffi.ffi_state 1))’] mp_tac) >>
    impl_tac
    >- (
      rgs [Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
      rgs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
      rgs [delay_rep_def, nexts_ffi_def]) >>
    strip_tac >> gvs [] >>
    (* isInput *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «isInput» _, nnnt)’ >>
    ‘nnnt.memory (t'.base_addr +  bytes_in_word) =
     Word (n2w (SND(t'.ffi.ffi_state 1)))’ by fs [Abbr ‘nnnt’] >>
    rgs [] >>
    ‘nnnt.memory (t'.base_addr +  bytes_in_word) = Word 0w’ by (
      rgs [delay_rep_def] >>
      fs [nexts_ffi_def]) >>
    fs [] >>
    drule evaluate_assign_compare_next_address >>
    rgs [] >>
    disch_then (qspecl_then [‘t'.base_addr’] mp_tac) >>
    impl_tac
    >- (
      rgs [Abbr ‘nnnt’, Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
      rgs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
      rgs [delay_rep_def, nexts_ffi_def]) >>
    strip_tac >> gvs [] >>
    (* If statement *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    drule evaluate_if_compare_sys_time >>
    disch_then (qspec_then ‘FST (nexts_ffi cycles t.ffi.ffi_state 1)’ mp_tac) >>
    impl_tac
    >- (
      unabbrev_all_tac >>
      rgs [FLOOKUP_UPDATE, nexts_ffi_def] >>
      rgs [delay_rep_def, ADD1]) >>
    strip_tac >> rveq >> rgs [] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    strip_tac >> fs [] >>
    rveq >> rgs [] >>
    unabbrev_all_tac >>
    rgs [] >> gvs [] >>
    reverse conj_tac
    >- (
      fs [ffi_call_ffi_def] >>
      fs [nexts_ffi_def, next_ffi_def, FLOOKUP_UPDATE] >>
      fs [ADD1] >>
      conj_asm1_tac
      >- (
        rgs [wait_time_locals1_def, FLOOKUP_UPDATE, mkState_def] >>
        qexists_tac ‘wt’ >>
        rgs [] >>
        gvs [delay_rep_def] >>
        qpat_x_assum ‘wakeup_rel _ _ _ _ _’ mp_tac >>
        rgs [wakeup_rel_def] >>
        strip_tac >>
        gvs [] >>
        first_x_assum (qspec_then ‘cycles + 1’ mp_tac) >>
        rgs [] >>
        strip_tac >>
        ‘w ≤ wt’ suffices_by gvs [] >>
        rgs [wakeup_shape_def] >>
        ‘wt' = wt’ suffices_by gvs [] >>
        drule sum_mod_eq_lt_eq >>
        rgs []) >>
      strip_tac >> rgs [] >>
      conj_asm1_tac
      >- (
        fs [delay_io_events_rel_def] >>
        conj_asm1_tac
        >- (
          qexists_tac ‘bytess ++ [bytes]’ >>
          rgs [] >>
          drule read_bytearray_LENGTH >>
          strip_tac >>
          conj_asm1_tac
          >- (
            rgs [ffiBufferSize_def, bytes_in_word_def] >>
            rgs [good_dimindex_def, dimword_def]) >>
          rgs [mk_ti_events_def] >>
          ‘gen_ffi_states t.ffi.ffi_state (LENGTH bytess + 1) =
           gen_ffi_states t.ffi.ffi_state (LENGTH bytess) ++
                          [(λn. t.ffi.ffi_state (n + LENGTH bytess))]’ by (
            fs [gen_ffi_states_def] >>
            rgs [GSYM ADD1, GENLIST]) >>
          rgs [] >>
          ‘LENGTH [bytes] = LENGTH [(λn. t.ffi.ffi_state (n + LENGTH bytess))] ∧
           LENGTH bytess = LENGTH (gen_ffi_states t.ffi.ffi_state (LENGTH bytess))’ by
            rgs [gen_ffi_states_def] >>
          drule ZIP_APPEND >>
          disch_then (qspecl_then [‘[bytes]’,
                                   ‘[(λn. t.ffi.ffi_state (n + LENGTH bytess))]’] mp_tac) >>
          impl_tac
          >- rgs [] >>
          strip_tac >>
          pop_assum (assume_tac o GSYM) >>
          rgs [mk_ti_event_def, time_input_def]) >>
        (* proving io_events rel *)
        rgs [from_io_events_def] >>
        rewrite_tac [GSYM APPEND_ASSOC] >>
        rgs [DROP_LENGTH_APPEND] >>
        rgs [mk_ti_events_def, io_events_dest_def] >>
        rgs [MAP_MAP_o] >>
        rgs [io_events_eq_ffi_seq_def] >>
        rgs [gen_ffi_states_def] >>
        rgs [EVERY_MEM] >>
        rw [] >> rgs []
        >- (
          rgs [MEM_MAP] >>
          drule MEM_ZIP2 >>
          strip_tac >> rgs [] >>
          rgs [mk_ti_event_def, io_event_dest_def] >>
          qmatch_goalsub_abbrev_tac ‘ZIP (nn, mm)’ >>
          ‘LENGTH nn = LENGTH mm’ by (
            fs [Abbr ‘nn’, Abbr ‘mm’] >>
            first_x_assum (qspec_then ‘EL n bytess'’ mp_tac) >>
            impl_tac
            >- (
              rgs [MEM_EL] >>
              metis_tac []) >>
            strip_tac >> rgs [] >>
            rgs [time_input_def, length_get_bytes] >>
            rgs [good_dimindex_def]) >>
          ‘MAP SND (ZIP (nn,mm)) = mm’ by (
            drule MAP_ZIP >>
            rgs []) >>
          rgs [] >>
          rgs [words_of_bytes_def] >>
          ‘8 ≤ dimindex (:α)’ by rgs [good_dimindex_def] >>
          drule LENGTH_words_of_bytes >>
          disch_then (qspecl_then [‘t.be’, ‘mm’] mp_tac) >>
          strip_tac >> rgs [] >>
          rgs [Abbr ‘mm’, time_input_def, length_get_bytes, bytes_in_word_def,
              good_dimindex_def, dimword_def])
        >- (
          qpat_x_assum ‘MAP _ _ ++ _ = _’ (assume_tac o GSYM) >>
          rgs [GSYM MAP_MAP_o] >>
          cases_on ‘i < LENGTH bytess’
          >- (
            last_x_assum (qspec_then ‘i’ mp_tac) >>
            impl_tac >- rgs [] >>
            strip_tac >>
            rgs [EL_APPEND_EQN]) >>
          rgs [EL_APPEND_EQN] >>
          ‘i − LENGTH bytess = 0’ by rgs [] >>
          simp [] >>
          rgs [io_event_dest_def] >>
          qmatch_goalsub_abbrev_tac ‘ZIP (nn, mm)’ >>
          ‘LENGTH nn = LENGTH mm’ by (
            fs [Abbr ‘nn’, Abbr ‘mm’] >>
            drule read_bytearray_LENGTH >>
            strip_tac >>
            rgs [length_get_bytes, ffiBufferSize_def,
                good_dimindex_def, bytes_in_word_def, dimword_def]) >>
          ‘MAP SND (ZIP (nn,mm)) = mm’ by (
            drule MAP_ZIP >>
            rgs []) >>
          rgs [Abbr ‘mm’] >>
          qmatch_goalsub_abbrev_tac ‘get_bytes t.be aa ++ get_bytes t.be bb’ >>
          ‘words_of_bytes t.be (get_bytes t.be aa ++ get_bytes t.be bb) =
           [aa;bb]’ by (
            match_mp_tac words_of_bytes_get_bytes >>
            rgs []) >>
          rgs [Abbr ‘aa’, Abbr ‘bb’] >>
          rgs [delay_rep_def] >>
          cases_on ‘t.ffi.ffi_state (i+1)’ >> rgs [] >>
          last_x_assum (qspec_then ‘i + 1’ mp_tac) >>
          rgs [] >>
          strip_tac >>
          qpat_x_assum ‘_ = d + FST (t.ffi.ffi_state 0)’ (mp_tac o GSYM) >>
          rgs [] >>
          strip_tac >>
          ‘LENGTH bytess = i’ by rgs [] >>
          simp []) >>
        rgs [decode_io_events_def] >>
        rgs [MAP_MAP_o] >>
        qmatch_goalsub_abbrev_tac ‘EL n (MAP f l)’ >>
        ‘EL n (MAP f l) = f (EL n l)’ by (
          match_mp_tac EL_MAP >>
          rgs [Abbr ‘f’, Abbr ‘l’]) >>
        rgs [Abbr ‘f’, Abbr ‘l’] >>
        qmatch_goalsub_abbrev_tac ‘ZIP (l1, l2)’ >>
        ‘EL n (ZIP (l1,l2)) = (EL n l1,EL n l2)’ by (
          match_mp_tac EL_ZIP >>
          rgs [Abbr ‘l1’, Abbr ‘l2’]) >>
        rgs [Abbr ‘l1’, Abbr ‘l2’] >>
        qmatch_goalsub_abbrev_tac ‘EL n (MAP f l)’ >>
        ‘EL n (MAP f l) = f (EL n l)’ by (
          match_mp_tac EL_MAP >>
          rgs [Abbr ‘f’, Abbr ‘l’]) >>
        rgs [Abbr ‘f’, Abbr ‘l’] >>
        rgs [mk_ti_event_def, decode_io_event_def] >>
        qmatch_goalsub_abbrev_tac ‘EL 1 nio’ >>
        ‘EL 1 nio = 0’ by (
          rgs [Abbr ‘nio’, io_event_dest_def] >>
          qmatch_goalsub_abbrev_tac ‘ZIP (nn, mm)’ >>
          ‘LENGTH nn = LENGTH mm’ by (
            fs [Abbr ‘nn’, Abbr ‘mm’] >>
            rgs [time_input_def, length_get_bytes] >>
            first_x_assum (qspec_then ‘EL n bytess'’ mp_tac) >>
            impl_tac >- metis_tac [MEM_EL] >>
            rgs [good_dimindex_def]) >>
          ‘MAP SND (ZIP (nn,mm)) = mm’ by (
            drule MAP_ZIP >>
            rgs []) >>
          rgs [Abbr ‘nn’, Abbr ‘mm’] >>
          rgs [time_input_def] >>
          qmatch_goalsub_abbrev_tac ‘get_bytes t.be aa ++ get_bytes t.be bb’ >>
          ‘words_of_bytes t.be (get_bytes t.be aa ++ get_bytes t.be bb) =
           [aa;bb]’ by (
            match_mp_tac words_of_bytes_get_bytes >>
            rgs []) >>
          rgs [Abbr ‘aa’, Abbr ‘bb’] >>
          rgs [delay_rep_def]) >>
        rgs [Abbr ‘nio’] >>
        rgs [io_event_dest_def] >>
        qmatch_goalsub_abbrev_tac ‘ZIP (nn, mm)’ >>
        ‘LENGTH nn = LENGTH mm’ by (
          fs [Abbr ‘nn’, Abbr ‘mm’] >>
          rgs [time_input_def, length_get_bytes] >>
          first_x_assum (qspec_then ‘EL n bytess'’ mp_tac) >>
          impl_tac >- metis_tac [MEM_EL] >>
          rgs [good_dimindex_def]) >>
        ‘MAP SND (ZIP (nn,mm)) = mm’ by (
          drule MAP_ZIP >>
          rgs []) >>
        rgs [Abbr ‘nn’, Abbr ‘mm’] >>
        rgs [time_input_def, length_get_bytes] >>
        qmatch_goalsub_abbrev_tac ‘get_bytes t.be aa ++ get_bytes t.be bb’ >>
        ‘words_of_bytes t.be (get_bytes t.be aa ++ get_bytes t.be bb) =
         [aa;bb]’ by (
          match_mp_tac words_of_bytes_get_bytes >>
          rgs []) >>
        rgs [Abbr ‘aa’, Abbr ‘bb’] >>
        last_x_assum assume_tac >>
        rgs [state_rel_def] >>
        pairarg_tac >> rgs [] >>
        rgs [time_seq_def]) >>
      rgs [obs_ios_are_label_delay_def] >>
      reverse conj_tac
      >- (
        pop_assum mp_tac >>
        once_rewrite_tac [delay_io_events_rel_def] >>
        fs [] >>
        strip_tac >>
        qmatch_goalsub_abbrev_tac ‘EL n ios’ >>
        strip_tac >>
        first_x_assum (qspec_then ‘n’ mp_tac) >>
        impl_tac
        >- (
          rgs [Abbr ‘ios’, Abbr ‘n’] >>
          rewrite_tac [GSYM APPEND_ASSOC] >>
          rgs [DROP_LENGTH_APPEND] >>
          rgs [decode_io_events_def, mk_ti_events_def, gen_ffi_states_def]) >>
        rgs [] >>
        strip_tac >>
        rgs [to_delay_def] >>
        rgs [Abbr ‘n’, Abbr ‘ios’, DROP_LENGTH_APPEND] >>
        rgs [decode_io_events_def, mk_ti_events_def, gen_ffi_states_def] >>
        rgs [delay_rep_def]) >>
      pop_assum mp_tac >>
      once_rewrite_tac [delay_io_events_rel_def] >>
      fs [] >>
      strip_tac >>
      simp [delay_ios_mono_def] >>
      rw [] >>
      last_x_assum assume_tac >>
      rgs [state_rel_def] >>
      pairarg_tac >> rgs [] >>
      rgs [time_seq_def] >>
      ‘(λx. FST (t.ffi.ffi_state x)) (i + 1) ≤ (λx. FST (t.ffi.ffi_state x)) (j + 1)’ by (
        match_mp_tac ffi_abs_mono >>
        rgs []) >>
      rgs []) >>
    (* proving state rel *)
    rgs [state_rel_def, mkState_def] >>
    conj_tac
    (* equivs *)
    >- rgs [equivs_def, FLOOKUP_UPDATE, active_low_def] >>
    conj_tac
    >- rgs [ffi_vars_def, FLOOKUP_UPDATE] >>
    conj_tac
    >- rgs [time_vars_def, FLOOKUP_UPDATE] >>
    conj_tac
    >- rgs [mem_config_def, mem_call_ffi_def] >>
    conj_tac
    >- (
    (* clock_bound *)
    qpat_x_assum ‘defined_clocks s.clocks _’ assume_tac >>
    rgs [defined_clocks_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    first_x_assum drule >>
    strip_tac >>
    fs [] >>
    fs [delay_clocks_def] >>
    qexists_tac ‘d+n’ >>
    rgs [] >>
    match_mp_tac mem_to_flookup >>
    ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
     MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
    fs [ALL_DISTINCT_fmap_to_alist_keys] >>
    fs [MEM_MAP] >>
    qexists_tac ‘(ck,n)’ >>
    fs []) >>
    pairarg_tac >> rgs [] >>
    conj_tac
    >- (
    fs [ffi_call_ffi_def, build_ffi_def] >>
    fs [ffiTheory.ffi_state_component_equality] >>
    last_x_assum assume_tac >>
    pairarg_tac >>
    fs [] >>
    pairarg_tac >>
    fs []) >>
    conj_tac
    >- (
    (* input_time_rel *)
    rgs [input_time_rel_def] >>
    rw [] >>
    rgs [input_time_eq_def, ffi_call_ffi_def, next_ffi_def, nexts_ffi_def,
        has_input_def] >>
    strip_tac >>
    pairarg_tac >> rgs [] >>
    first_x_assum (qspec_then ‘n+1’ mp_tac) >>
    impl_tac >- rgs [] >>
    rgs []) >>
    conj_tac
    >- (
    (* time_seq holds *)
    rgs [ffi_call_ffi_def,
        nexts_ffi_def, next_ffi_def] >>
    last_x_assum mp_tac >>
    pairarg_tac >> rgs [] >>
    strip_tac >>
    drule time_seq_add_holds >>
    disch_then (qspec_then ‘cycles + 1’ mp_tac) >>
    fs [])  >>
    rgs [clocks_rel_def, FLOOKUP_UPDATE, nexts_ffi_def,
        ffi_call_ffi_def, next_ffi_def, time_seq_def] >>
    pairarg_tac >> rgs [] >> rveq >> rgs [] >>
    qexists_tac ‘ns’ >>
    fs [] >>
    fs [clkvals_rel_def] >>
    conj_tac
    >- (
    fs [MAP_EQ_EVERY2] >>
    fs [LIST_REL_EL_EQN] >>
    rw [] >>
    pairarg_tac >> fs [] >>
    last_x_assum drule >>
    fs [] >>
    strip_tac >>
    (* shortcut *)
    ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
      drule EL_ZIP >>
      disch_then (qspec_then ‘n’ mp_tac) >>
      rgs [] >>
      strip_tac >>
      rgs [defined_clocks_def] >>
      fs [EVERY_MEM] >>
      fs [MEM_EL] >>
      last_x_assum (qspec_then ‘x’ mp_tac) >>
      fs [] >>
      impl_tac >- metis_tac [] >>
      rgs [FDOM_FLOOKUP]) >>
    fs [delay_clocks_def] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
     x = SOME (d + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
     x = SOME (sd + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    fs [ffi_call_ffi_def, next_ffi_def] >>
    qpat_x_assum ‘delay_rep d _ _’ assume_tac >>
    qpat_x_assum ‘delay_rep sd _ _’ assume_tac >>
    qpat_x_assum ‘sd ≤ d’ assume_tac >>
    rgs [delay_rep_def] >>
    rgs [ADD1]) >>
    fs [EVERY_MEM] >>
    rw [] >>
    first_x_assum (qspec_then ‘x’ assume_tac) >>
    rgs [] >>
    ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
      rgs [defined_clocks_def] >>
      rgs [EVERY_MEM]) >>
    fs [delay_clocks_def] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
     x = SOME (d + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
     x = SOME (sd + xn)’ by (
      match_mp_tac mem_to_flookup >>
      ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
       MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
      fs [ALL_DISTINCT_fmap_to_alist_keys] >>
      fs [MEM_MAP] >>
      qexists_tac ‘(x,xn)’ >>
      fs []) >>
    fs [] >>
    fs [ffi_call_ffi_def, next_ffi_def] >>
    qpat_x_assum ‘delay_rep d _ _’ assume_tac >>
    qpat_x_assum ‘delay_rep sd _ _’ assume_tac >>
    qpat_x_assum ‘sd ≤ d’ assume_tac >>
    rgs [delay_rep_def] >>
    rgs [ADD1]) >> (* case d < w 1 end *)
  ‘d = w’ by rgs [] >>
  pop_assum mp_tac >>
  pop_assum kall_tac >>
  qpat_x_assum ‘d ≤ w’ kall_tac >>
  strip_tac >>
  qexists_tac ‘ck’ >>
  fs [] >>
  qpat_x_assum ‘∀ck_extra. _’ kall_tac >>
  drule state_rel_imp_mem_config >>
  rewrite_tac [Once mem_config_def] >>
  strip_tac >>
  fs [] >>
  ‘∃bytes.
     read_bytearray t'.base_addr (w2n (ffiBufferSize:'a word))
                    (mem_load_byte t'.memory t'.memaddrs t'.be) = SOME bytes’ by (
    match_mp_tac read_bytearray_some_bytes_for_ffi >>
    rgs [state_rel_def]) >>
  qabbrev_tac
  ‘new_t:('a,time_input) panSem$state =
         t' with
            <|locals :=
              t'.locals |+
                («sysTime» ,
                 ValWord (n2w (FST (nexts_ffi cycles t.ffi.ffi_state 1)))) |+
                («event» ,
                 ValWord (n2w (SND (nexts_ffi cycles t.ffi.ffi_state 1)))) |+
                («isInput» ,ValWord 1w);

              memory :=
              mem_call_ffi (:α) t'.memory t'.memaddrs t.be t.base_addr
                           (nexts_ffi cycles t.ffi.ffi_state);
              ffi := ffi_call_ffi (:α) t.be t'.ffi bytes|>’ >>
  qexists_tac ‘new_t’ >>
  fs [PULL_FORALL] >>
  gen_tac >> rgs [] >>
  fs [wait_input_time_limit_def] >>
  rewrite_tac [Once evaluate_def] >>
  drule step_wait_delay_eval_wait_not_zero >>
  impl_tac
  >- (
    conj_tac
    >- rgs [state_rel_def, mkState_def, equivs_def, active_low_def] >>
    rgs [] >>
    rgs [wakeup_rel_def, delay_rep_def] >>
    qexists_tac ‘sd + FST (t.ffi.ffi_state 0)’ >>
    rgs [] >>
    qexists_tac ‘(ist + w) - (sd +  FST (t.ffi.ffi_state 0))’ >>
    rgs [] >>
    ‘ist + w − (sd + FST (t.ffi.ffi_state 0)) + FST (t.ffi.ffi_state 0) =
     ist + w − sd’ by (
        once_rewrite_tac [SUB_PLUS] >>
        ‘FST (t.ffi.ffi_state 0) ≤ ist + w − sd’ by (
          rgs [] >>
          first_x_assum (qspec_then ‘cycles’ mp_tac) >>
          rgs []) >>
        drule SUB_ADD >>
        rgs []) >>
    fs [] >>
    first_x_assum (qspec_then ‘cycles’ mp_tac) >>
    rgs []) >>
  strip_tac >>
  rgs [eval_upd_clock_eq] >>
  (* evaluating the function *)
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  fs [dec_clock_def] >>
  rewrite_tac [Once check_input_time_def] >>
  fs [panLangTheory.nested_seq_def] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  drule evaluate_ext_call >>
  disch_then (qspecl_then [‘MAP explode (out_signals prog)’,‘bytes’] mp_tac) >>
  impl_tac
  >- (
    rgs [state_rel_def] >>
    pairarg_tac >> rgs []) >>
  strip_tac >> gvs [] >>
  drule state_rel_imp_ffi_vars >>
  strip_tac >>
  pop_assum mp_tac >>
  rewrite_tac [Once ffi_vars_def] >>
  strip_tac >>
  drule state_rel_imp_systime_defined >>
  strip_tac >>
  (* reading systime *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
  ‘nt.memory t'.base_addr = Word (n2w (FST(t'.ffi.ffi_state 1)))’ by (
    fs [Abbr ‘nt’] >>
    qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
    rgs [mem_read_ffi_results_def] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
    last_x_assum
    (qspecl_then
     [‘cycles’,
      ‘t' with clock := ck0 + ck_extra + t'.clock’,
      ‘ft’] mp_tac)>>
    impl_tac
    >- rgs [Abbr ‘ft’] >>
    strip_tac >>
    rgs [Abbr ‘ft’]) >>
  drule evaluate_assign_load >>
  rgs [] >>
  disch_then (qspecl_then
              [‘t'.base_addr’, ‘tm’,
               ‘n2w (FST (t'.ffi.ffi_state 1))’] mp_tac) >>
  impl_tac
  >- (
    rgs [Abbr ‘nt’] >>
    fs [state_rel_def]) >>
  strip_tac >> gvs [] >>
  (* reading input to the variable event *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «event» _, nnt)’ >>
  ‘nnt.memory (t'.base_addr +  bytes_in_word) =
   Word (n2w (SND(t'.ffi.ffi_state 1)))’ by (
    fs [Abbr ‘nnt’, Abbr ‘nt’] >>
    qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
    rgs [mem_read_ffi_results_def] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
    last_x_assum
    (qspecl_then
     [‘cycles’,
      ‘t' with clock := ck0 + ck_extra + t'.clock’,
      ‘ft’] mp_tac)>>
    impl_tac
    >- rgs [Abbr ‘ft’] >>
    strip_tac >>
    rgs [Abbr ‘ft’]) >>
  rgs [] >>
  drule evaluate_assign_load_next_address >>
  rgs [] >>
  disch_then (qspecl_then
              [‘t.base_addr’,
               ‘n2w (SND (nexts_ffi cycles t.ffi.ffi_state 1))’] mp_tac) >>
  impl_tac
  >- (
    rgs [Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
    rgs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
    rgs [delay_rep_def, nexts_ffi_def]) >>
  strip_tac >> gvs [] >>
  (* isInput *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «isInput» _, nnnt)’ >>
  ‘nnnt.memory (t'.base_addr +  bytes_in_word) =
   Word (n2w (SND(t'.ffi.ffi_state 1)))’ by fs [Abbr ‘nnnt’] >>
  rgs [] >>
  ‘nnnt.memory (t'.base_addr +  bytes_in_word) = Word 0w’ by (
    rgs [delay_rep_def] >>
    fs [nexts_ffi_def]) >>
  fs [] >>
  drule evaluate_assign_compare_next_address >>
  rgs [] >>
  disch_then (qspecl_then [‘t'.base_addr’] mp_tac) >>
  impl_tac
  >- (
  rgs [Abbr ‘nnnt’, Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
  rgs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
  rgs [delay_rep_def, nexts_ffi_def]) >>
  strip_tac >> gvs [] >>
  (* If statement *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  drule evaluate_if_compare_sys_time >>
  disch_then (qspec_then ‘FST (nexts_ffi cycles t.ffi.ffi_state 1)’ mp_tac) >>
  impl_tac
  >- (
    unabbrev_all_tac >>
    rgs [FLOOKUP_UPDATE, nexts_ffi_def] >>
    rgs [delay_rep_def, ADD1]) >>
  strip_tac >> rveq >> rgs [] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  strip_tac >> fs [] >>
  rveq >> rgs [] >>
  unabbrev_all_tac >>
  rgs [] >> gvs [] >>
  reverse conj_tac
  >- (
      fs [ffi_call_ffi_def] >>
      fs [nexts_ffi_def, next_ffi_def, FLOOKUP_UPDATE] >>
      fs [ADD1] >>
      conj_asm1_tac
      >- (
        rgs [wait_time_locals1_def, FLOOKUP_UPDATE, mkState_def] >>
        qexists_tac ‘wt’ >>
        rgs [] >>
        gvs [delay_rep_def]) >>
      strip_tac >> rgs [] >>
      conj_asm1_tac
      >- (
        fs [delay_io_events_rel_def] >>
        conj_asm1_tac
        >- (
          qexists_tac ‘bytess ++ [bytes]’ >>
          rgs [] >>
          drule read_bytearray_LENGTH >>
          strip_tac >>
          conj_asm1_tac
          >- (
            rgs [ffiBufferSize_def, bytes_in_word_def] >>
            rgs [good_dimindex_def, dimword_def]) >>
          rgs [mk_ti_events_def] >>
          ‘gen_ffi_states t.ffi.ffi_state (LENGTH bytess + 1) =
           gen_ffi_states t.ffi.ffi_state (LENGTH bytess) ++
                          [(λn. t.ffi.ffi_state (n + LENGTH bytess))]’ by (
            fs [gen_ffi_states_def] >>
            rgs [GSYM ADD1, GENLIST]) >>
          rgs [] >>
          ‘LENGTH [bytes] = LENGTH [(λn. t.ffi.ffi_state (n + LENGTH bytess))] ∧
           LENGTH bytess = LENGTH (gen_ffi_states t.ffi.ffi_state (LENGTH bytess))’ by
            rgs [gen_ffi_states_def] >>
          drule ZIP_APPEND >>
          disch_then (qspecl_then [‘[bytes]’,
                                   ‘[(λn. t.ffi.ffi_state (n + LENGTH bytess))]’] mp_tac) >>
          impl_tac
          >- rgs [] >>
          strip_tac >>
          pop_assum (assume_tac o GSYM) >>
          rgs [mk_ti_event_def, time_input_def]) >>
        (* proving io_events rel *)
        rgs [from_io_events_def] >>
        rewrite_tac [GSYM APPEND_ASSOC] >>
        rgs [DROP_LENGTH_APPEND] >>
        rgs [mk_ti_events_def, io_events_dest_def] >>
        rgs [MAP_MAP_o] >>
        rgs [io_events_eq_ffi_seq_def] >>
        rgs [gen_ffi_states_def] >>
        rgs [EVERY_MEM] >>
        rw [] >> rgs []
        >- (
          rgs [MEM_MAP] >>
          drule MEM_ZIP2 >>
          strip_tac >> rgs [] >>
          rgs [mk_ti_event_def, io_event_dest_def] >>
          qmatch_goalsub_abbrev_tac ‘ZIP (nn, mm)’ >>
          ‘LENGTH nn = LENGTH mm’ by (
            fs [Abbr ‘nn’, Abbr ‘mm’] >>
            first_x_assum (qspec_then ‘EL n bytess'’ mp_tac) >>
            impl_tac
            >- (
              rgs [MEM_EL] >>
              metis_tac []) >>
            strip_tac >> rgs [] >>
            rgs [time_input_def, length_get_bytes] >>
            rgs [good_dimindex_def]) >>
          ‘MAP SND (ZIP (nn,mm)) = mm’ by (
            drule MAP_ZIP >>
            rgs []) >>
          rgs [] >>
          rgs [words_of_bytes_def] >>
          ‘8 ≤ dimindex (:α)’ by rgs [good_dimindex_def] >>
          drule LENGTH_words_of_bytes >>
          disch_then (qspecl_then [‘t.be’, ‘mm’] mp_tac) >>
          strip_tac >> rgs [] >>
          rgs [Abbr ‘mm’, time_input_def, length_get_bytes, bytes_in_word_def,
              good_dimindex_def, dimword_def])
        >- (
          qpat_x_assum ‘MAP _ _ ++ _ = _’ (assume_tac o GSYM) >>
          rgs [GSYM MAP_MAP_o] >>
          cases_on ‘i < LENGTH bytess’
          >- (
            last_x_assum (qspec_then ‘i’ mp_tac) >>
            impl_tac >- rgs [] >>
            strip_tac >>
            rgs [EL_APPEND_EQN]) >>
          rgs [EL_APPEND_EQN] >>
          ‘i − LENGTH bytess = 0’ by rgs [] >>
          simp [] >>
          rgs [io_event_dest_def] >>
          qmatch_goalsub_abbrev_tac ‘ZIP (nn, mm)’ >>
          ‘LENGTH nn = LENGTH mm’ by (
            fs [Abbr ‘nn’, Abbr ‘mm’] >>
            drule read_bytearray_LENGTH >>
            strip_tac >>
            rgs [length_get_bytes, ffiBufferSize_def,
                good_dimindex_def, bytes_in_word_def, dimword_def]) >>
          ‘MAP SND (ZIP (nn,mm)) = mm’ by (
            drule MAP_ZIP >>
            rgs []) >>
          rgs [Abbr ‘mm’] >>
          qmatch_goalsub_abbrev_tac ‘get_bytes t.be aa ++ get_bytes t.be bb’ >>
          ‘words_of_bytes t.be (get_bytes t.be aa ++ get_bytes t.be bb) =
           [aa;bb]’ by (
            match_mp_tac words_of_bytes_get_bytes >>
            rgs []) >>
          rgs [Abbr ‘aa’, Abbr ‘bb’] >>
          rgs [delay_rep_def] >>
          cases_on ‘t.ffi.ffi_state (i+1)’ >> rgs [] >>
          last_x_assum (qspec_then ‘i + 1’ mp_tac) >>
          rgs [] >>
          strip_tac >>
          qpat_x_assum ‘_ = d + FST (t.ffi.ffi_state 0)’ (mp_tac o GSYM) >>
          rgs [] >>
          strip_tac >>
          ‘LENGTH bytess = i’ by rgs [] >>
          simp []) >>
        rgs [decode_io_events_def] >>
        rgs [MAP_MAP_o] >>
        qmatch_goalsub_abbrev_tac ‘EL n (MAP f l)’ >>
        ‘EL n (MAP f l) = f (EL n l)’ by (
          match_mp_tac EL_MAP >>
          rgs [Abbr ‘f’, Abbr ‘l’]) >>
        rgs [Abbr ‘f’, Abbr ‘l’] >>
        qmatch_goalsub_abbrev_tac ‘ZIP (l1, l2)’ >>
        ‘EL n (ZIP (l1,l2)) = (EL n l1,EL n l2)’ by (
          match_mp_tac EL_ZIP >>
          rgs [Abbr ‘l1’, Abbr ‘l2’]) >>
        rgs [Abbr ‘l1’, Abbr ‘l2’] >>
        qmatch_goalsub_abbrev_tac ‘EL n (MAP f l)’ >>
        ‘EL n (MAP f l) = f (EL n l)’ by (
          match_mp_tac EL_MAP >>
          rgs [Abbr ‘f’, Abbr ‘l’]) >>
        rgs [Abbr ‘f’, Abbr ‘l’] >>
        rgs [mk_ti_event_def, decode_io_event_def] >>
        qmatch_goalsub_abbrev_tac ‘EL 1 nio’ >>
        ‘EL 1 nio = 0’ by (
          rgs [Abbr ‘nio’, io_event_dest_def] >>
          qmatch_goalsub_abbrev_tac ‘ZIP (nn, mm)’ >>
          ‘LENGTH nn = LENGTH mm’ by (
            fs [Abbr ‘nn’, Abbr ‘mm’] >>
            rgs [time_input_def, length_get_bytes] >>
            first_x_assum (qspec_then ‘EL n bytess'’ mp_tac) >>
            impl_tac >- metis_tac [MEM_EL] >>
            rgs [good_dimindex_def]) >>
          ‘MAP SND (ZIP (nn,mm)) = mm’ by (
            drule MAP_ZIP >>
            rgs []) >>
          rgs [Abbr ‘nn’, Abbr ‘mm’] >>
          rgs [time_input_def] >>
          qmatch_goalsub_abbrev_tac ‘get_bytes t.be aa ++ get_bytes t.be bb’ >>
          ‘words_of_bytes t.be (get_bytes t.be aa ++ get_bytes t.be bb) =
           [aa;bb]’ by (
            match_mp_tac words_of_bytes_get_bytes >>
            rgs []) >>
          rgs [Abbr ‘aa’, Abbr ‘bb’] >>
          rgs [delay_rep_def]) >>
        rgs [Abbr ‘nio’] >>
        rgs [io_event_dest_def] >>
        qmatch_goalsub_abbrev_tac ‘ZIP (nn, mm)’ >>
        ‘LENGTH nn = LENGTH mm’ by (
          fs [Abbr ‘nn’, Abbr ‘mm’] >>
          rgs [time_input_def, length_get_bytes] >>
          first_x_assum (qspec_then ‘EL n bytess'’ mp_tac) >>
          impl_tac >- metis_tac [MEM_EL] >>
          rgs [good_dimindex_def]) >>
        ‘MAP SND (ZIP (nn,mm)) = mm’ by (
          drule MAP_ZIP >>
          rgs []) >>
        rgs [Abbr ‘nn’, Abbr ‘mm’] >>
        rgs [time_input_def, length_get_bytes] >>
        qmatch_goalsub_abbrev_tac ‘get_bytes t.be aa ++ get_bytes t.be bb’ >>
        ‘words_of_bytes t.be (get_bytes t.be aa ++ get_bytes t.be bb) =
         [aa;bb]’ by (
          match_mp_tac words_of_bytes_get_bytes >>
          rgs []) >>
        rgs [Abbr ‘aa’, Abbr ‘bb’] >>
        last_x_assum assume_tac >>
        rgs [state_rel_def] >>
        pairarg_tac >> rgs [] >>
        rgs [time_seq_def]) >>
      rgs [obs_ios_are_label_delay_def] >>
      reverse conj_tac
      >- (
        pop_assum mp_tac >>
        once_rewrite_tac [delay_io_events_rel_def] >>
        fs [] >>
        strip_tac >>
        qmatch_goalsub_abbrev_tac ‘EL n ios’ >>
        strip_tac >>
        first_x_assum (qspec_then ‘n’ mp_tac) >>
        impl_tac
        >- (
          rgs [Abbr ‘ios’, Abbr ‘n’] >>
          rewrite_tac [GSYM APPEND_ASSOC] >>
          rgs [DROP_LENGTH_APPEND] >>
          rgs [decode_io_events_def, mk_ti_events_def, gen_ffi_states_def]) >>
        rgs [] >>
        strip_tac >>
        rgs [to_delay_def] >>
        rgs [Abbr ‘n’, Abbr ‘ios’, DROP_LENGTH_APPEND] >>
        rgs [decode_io_events_def, mk_ti_events_def, gen_ffi_states_def] >>
        rgs [delay_rep_def]) >>
      pop_assum mp_tac >>
      once_rewrite_tac [delay_io_events_rel_def] >>
      fs [] >>
      strip_tac >>
      simp [delay_ios_mono_def] >>
      rw [] >>
      last_x_assum assume_tac >>
      rgs [state_rel_def] >>
      pairarg_tac >> rgs [] >>
      rgs [time_seq_def] >>
      ‘(λx. FST (t.ffi.ffi_state x)) (i + 1) ≤ (λx. FST (t.ffi.ffi_state x)) (j + 1)’ by (
        match_mp_tac ffi_abs_mono >>
        rgs []) >>
      rgs []) >>
  (* proving state rel *)
  rgs [state_rel_def, mkState_def] >>
  conj_tac
  (* equivs *)
  >- rgs [equivs_def, FLOOKUP_UPDATE, active_low_def] >>
  conj_tac
  >- rgs [ffi_vars_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- rgs [time_vars_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- rgs [mem_config_def, mem_call_ffi_def] >>
  conj_tac
  >- (
  (* clock_bound *)
  qpat_x_assum ‘defined_clocks s.clocks _’ assume_tac >>
  rgs [defined_clocks_def] >>
  fs [EVERY_MEM] >>
  rw [] >>
  first_x_assum drule >>
  strip_tac >>
  fs [] >>
  fs [delay_clocks_def] >>
  qexists_tac ‘d+n’ >>
  rgs [] >>
  match_mp_tac mem_to_flookup >>
  ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
   MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
  fs [ALL_DISTINCT_fmap_to_alist_keys] >>
  fs [MEM_MAP] >>
  qexists_tac ‘(ck,n)’ >>
  fs []) >>
  pairarg_tac >> rgs [] >>
  conj_tac
  >- (
  fs [ffi_call_ffi_def, build_ffi_def] >>
  fs [ffiTheory.ffi_state_component_equality] >>
  last_x_assum assume_tac >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs []) >>
  conj_tac
  >- (
  (* input_time_rel *)
  rgs [input_time_rel_def] >>
  rw [] >>
  rgs [input_time_eq_def, ffi_call_ffi_def, next_ffi_def, nexts_ffi_def,
      has_input_def] >>
  strip_tac >>
  pairarg_tac >> rgs [] >>
  first_x_assum (qspec_then ‘n+1’ mp_tac) >>
  impl_tac >- rgs [] >>
  rgs []) >>
  conj_tac
  >- (
  (* time_seq holds *)
  rgs [ffi_call_ffi_def,
      nexts_ffi_def, next_ffi_def] >>
  last_x_assum mp_tac >>
  pairarg_tac >> rgs [] >>
  strip_tac >>
  drule time_seq_add_holds >>
  disch_then (qspec_then ‘cycles + 1’ mp_tac) >>
  fs [])  >>
  rgs [clocks_rel_def, FLOOKUP_UPDATE, nexts_ffi_def,
      ffi_call_ffi_def, next_ffi_def, time_seq_def] >>
  pairarg_tac >> rgs [] >> rveq >> rgs [] >>
  qexists_tac ‘ns’ >>
  fs [] >>
  fs [clkvals_rel_def] >>
  conj_tac
  >- (
  fs [MAP_EQ_EVERY2] >>
  fs [LIST_REL_EL_EQN] >>
  rw [] >>
  pairarg_tac >> fs [] >>
  last_x_assum drule >>
  fs [] >>
  strip_tac >>
  (* shortcut *)
  ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
    drule EL_ZIP >>
    disch_then (qspec_then ‘n’ mp_tac) >>
    rgs [] >>
    strip_tac >>
    rgs [defined_clocks_def] >>
    fs [EVERY_MEM] >>
    fs [MEM_EL] >>
    last_x_assum (qspec_then ‘x’ mp_tac) >>
    fs [] >>
    impl_tac >- metis_tac [] >>
    rgs [FDOM_FLOOKUP]) >>
  fs [delay_clocks_def] >>
  ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
   x = SOME (d + xn)’ by (
    match_mp_tac mem_to_flookup >>
    ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
     MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
    fs [ALL_DISTINCT_fmap_to_alist_keys] >>
    fs [MEM_MAP] >>
    qexists_tac ‘(x,xn)’ >>
    fs []) >>
  fs [] >>
  ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
   x = SOME (sd + xn)’ by (
    match_mp_tac mem_to_flookup >>
    ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
     MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
    fs [ALL_DISTINCT_fmap_to_alist_keys] >>
    fs [MEM_MAP] >>
    qexists_tac ‘(x,xn)’ >>
    fs []) >>
  fs [] >>
  fs [ffi_call_ffi_def, next_ffi_def] >>
  qpat_x_assum ‘delay_rep d _ _’ assume_tac >>
  qpat_x_assum ‘delay_rep sd _ _’ assume_tac >>
  qpat_x_assum ‘sd ≤ d’ assume_tac >>
  rgs [delay_rep_def] >>
  rgs [ADD1]) >>
  fs [EVERY_MEM] >>
  rw [] >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  rgs [] >>
  ‘∃xn. FLOOKUP s.clocks x = SOME xn’ by (
    rgs [defined_clocks_def] >>
    rgs [EVERY_MEM]) >>
  fs [delay_clocks_def] >>
  ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks))
   x = SOME (d + xn)’ by (
    match_mp_tac mem_to_flookup >>
    ‘MAP FST (MAP (λ(x,y). (x,d + y)) (fmap_to_alist s.clocks)) =
     MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
    fs [ALL_DISTINCT_fmap_to_alist_keys] >>
    fs [MEM_MAP] >>
    qexists_tac ‘(x,xn)’ >>
    fs []) >>
  fs [] >>
  ‘FLOOKUP (FEMPTY |++ MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks))
   x = SOME (sd + xn)’ by (
    match_mp_tac mem_to_flookup >>
    ‘MAP FST (MAP (λ(x,y). (x,sd + y)) (fmap_to_alist s.clocks)) =
     MAP FST (fmap_to_alist s.clocks)’ by fs [map_fst] >>
    fs [ALL_DISTINCT_fmap_to_alist_keys] >>
    fs [MEM_MAP] >>
    qexists_tac ‘(x,xn)’ >>
    fs []) >>
  fs [] >>
  fs [ffi_call_ffi_def, next_ffi_def] >>
  qpat_x_assum ‘delay_rep d _ _’ assume_tac >>
  qpat_x_assum ‘delay_rep sd _ _’ assume_tac >>
  qpat_x_assum ‘sd ≤ d’ assume_tac >>
  rgs [delay_rep_def] >>
  rgs [ADD1]
QED


Theorem evaluate_seq_fst:
  evaluate (p, t) = evaluate (p, t') ⇒
  evaluate (Seq p q, t) = evaluate (Seq p q, t')
Proof
  rw [] >>
  fs [evaluate_def]
QED


Theorem step_delay:
  !cycles prog d m n s s' (t:('a,time_input) panSem$state) ck0 ist.
    step prog (LDelay d) m n s s' ∧
    m = dimword (:α) - 1 ∧ n = FST (t.ffi.ffi_state 0) ∧
    state_rel (clksOf prog) (out_signals prog) s t ∧
    code_installed t.code prog ∧
    delay_rep d t.ffi.ffi_state cycles ∧
    wakeup_shape t.locals s.waitTime ist ∧
    wakeup_rel t.locals s.waitTime ist t.ffi.ffi_state cycles ∧
    mem_read_ffi_results (:α) t.ffi.ffi_state cycles ∧
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «event» =  SOME (ValWord 0w) ∧
    good_dimindex (:'a) ==>
    ?ck t'.
      (∀ck_extra.
         evaluate (task_controller (nClks prog), t with clock := t.clock + ck + ck_extra) =
         evaluate (task_controller (nClks prog), t' with clock := t'.clock + ck_extra + ck0)) ∧
      code_installed t'.code prog ∧
      state_rel (clksOf prog) (out_signals prog) s' t' ∧
      t'.ffi.ffi_state = nexts_ffi cycles t.ffi.ffi_state ∧
      t'.ffi.oracle = t.ffi.oracle ∧
      t'.code = t.code ∧
      t'.be = t.be ∧ t'.base_addr = t.base_addr ∧
      t'.eshapes = t.eshapes ∧
      FLOOKUP t'.locals «wakeUpAt» = FLOOKUP t.locals «wakeUpAt» ∧
      FLOOKUP t'.locals «waitSet» = FLOOKUP t.locals «waitSet» ∧
      FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
      FLOOKUP t'.locals «event» =  SOME (ValWord 0w) ∧
      FLOOKUP t'.locals «taskRet» = FLOOKUP t.locals «taskRet» ∧
      FLOOKUP t'.locals «sysTime»  =
      SOME (ValWord (n2w (FST (t.ffi.ffi_state cycles)))) ∧
      wait_time_locals1 (:α) t'.locals s'.waitTime ist
                        (FST (t.ffi.ffi_state cycles)) ∧
      (t.ffi.io_events ≠ [] ∧
       EL 0 (io_event_dest (:α) t.be (LAST t.ffi.io_events)) = FST (t.ffi.ffi_state 0) ⇒
       delay_io_events_rel t t' cycles ∧
      obs_ios_are_label_delay d t t')
Proof
  rw [] >>
  fs [task_controller_def] >>
  fs [panLangTheory.nested_seq_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  drule step_delay_loop >>
  disch_then (qspecl_then [‘cycles’, ‘t’, ‘ck0’, ‘ist’] mp_tac) >>
  fs [] >>
  strip_tac >>
  qexists_tac ‘ck’ >> fs [] >>
  qexists_tac ‘t'’ >> fs [] >>
  rw [] >>
  first_x_assum (qspec_then ‘ck_extra’ assume_tac) >>
  drule evaluate_seq_fst >>
  disch_then (qspec_then ‘q’ assume_tac) >>
  gs []
QED


Theorem step_input_eval_wait_zero:
  !t.
    FLOOKUP t.locals «isInput» = SOME (ValWord 0w) ∧
    (?tm. FLOOKUP t.locals «waitSet» = SOME (ValWord tm)) ∧
    (?st. FLOOKUP t.locals «sysTime» = SOME (ValWord st)) ∧
    (?wt. FLOOKUP t.locals «wakeUpAt» = SOME (ValWord wt)) ==>
    ?w.
      eval t wait = SOME (ValWord w) ∧
      w = 0w
Proof
  rw [] >>
  fs [wait_def, eval_def, OPT_MMAP_def] >>
  gs [wordLangTheory.word_op_def]
QED


Theorem step_delay_eval_wait_zero:
  !t st.
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «waitSet» = SOME (ValWord 0w) ∧
    FLOOKUP t.locals «sysTime» = SOME (ValWord st) ∧
    FLOOKUP t.locals «wakeUpAt» = SOME (ValWord st) ==>
    ?w.
      eval t wait = SOME (ValWord w) ∧
      w = 0w
Proof
  rw [] >>
  fs [wait_def, eval_def, OPT_MMAP_def] >>
  gs [wordLangTheory.word_op_def] >>
  fs [asmTheory.word_cmp_def]
QED

Theorem eval_normalisedClks:
  ∀t st ns.
    FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w st)) ∧
    FLOOKUP t.locals «clks» = SOME (Struct (MAP (ValWord o n2w) ns)) ∧
    EVERY (λn. n ≤ st) ns ⇒
      OPT_MMAP (eval t) (normalisedClks «sysTime» «clks» (LENGTH ns)) =
      SOME (MAP (λ(x,y). ValWord (n2w (x-y))) (ZIP (REPLICATE (LENGTH ns) st,ns)))
     (* MAP is better for reasoning than MAP2*)
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [normalisedClks_def] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2] >>
  conj_tac
  >- fs [mkClks_def, fieldsOf_def] >>
  fs [LIST_REL_EL_EQN] >>
  conj_tac
  >- fs [mkClks_def, fieldsOf_def] >>
  rw [] >>
  qmatch_goalsub_abbrev_tac ‘MAP2 ff xs ys’ >>
  ‘EL n (MAP2 ff xs ys) = ff (EL n xs) (EL n ys)’ by (
    match_mp_tac EL_MAP2 >>
    fs []) >>
  unabbrev_all_tac >>
  gs [] >>
  qmatch_goalsub_abbrev_tac ‘MAP ff (ZIP (xs,ys))’ >>
  ‘EL n (MAP ff (ZIP (xs,ys))) = ff (EL n (ZIP (xs,ys)))’ by (
    match_mp_tac EL_MAP >>
    unabbrev_all_tac >>
    gs [mkClks_def]) >>
  unabbrev_all_tac >>
  gs [] >>
  fs [mkClks_def, fieldsOf_def] >>
  ‘EL n (ZIP (REPLICATE (LENGTH ns) st,ns)) =
   (EL n (REPLICATE (LENGTH ns) st),EL n ns)’ by (
    match_mp_tac EL_ZIP >>
    fs []) >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
  ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
    match_mp_tac EL_MAP >>
    unabbrev_all_tac >>
    gs [mkClks_def]) >>
  fs [] >>
  unabbrev_all_tac >>
  ‘EL n (GENLIST I (LENGTH ns)) = I n’ by (
    match_mp_tac EL_GENLIST >>
    gs []) >>
  fs [] >>
  ‘EL n (REPLICATE (LENGTH ns) (Var «sysTime»)) = Var «sysTime»’ by (
    match_mp_tac EL_REPLICATE >>
    gs []) >>
  fs [] >>
  ‘EL n (REPLICATE (LENGTH ns) st) = st’ by (
    match_mp_tac EL_REPLICATE >>
    gs []) >>
  fs [] >>
  gs [eval_def,  OPT_MMAP_def] >>
  qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
  ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
    match_mp_tac EL_MAP >>
    unabbrev_all_tac >>
    gs []) >>
  unabbrev_all_tac >>
  gs [] >>
  fs [wordLangTheory.word_op_def] >>
  fs [EVERY_MEM] >>
  first_x_assum (qspec_then ‘EL n ns’ mp_tac) >>
  gs [MEM_EL] >>
  impl_tac >- metis_tac [] >>
  strip_tac >>
  drule n2w_sub >>
  strip_tac >> fs []
QED


Theorem genshape_eq_shape_of:
  ∀ys x zs.
    LENGTH ys = LENGTH zs ⇒
    genShape (LENGTH ys) =
      shape_of (Struct
                (MAP (λ(x,y). ValWord (n2w (x − y)))
                 (ZIP (REPLICATE (LENGTH ys) x,zs))))
Proof
  rw [] >>
  fs [genShape_def] >>
  fs [shape_of_def] >>
  ‘REPLICATE (LENGTH ys) One = MAP (λx. One) (GENLIST I (LENGTH ys))’ by (
    fs [MAP_GENLIST] >>
    fs [REPLICATE_GENLIST] >>
    fs [seqTheory.K_PARTIAL]) >>
  gs [] >>
  fs [MAP_EQ_EVERY2] >>
  fs [LIST_REL_EL_EQN] >>
  rw [] >>
  qmatch_goalsub_abbrev_tac ‘MAP ff (ZIP (xs,_))’ >>
  ‘EL n (MAP ff (ZIP (xs,zs))) = ff (EL n (ZIP (xs,zs)))’ by (
    match_mp_tac EL_MAP >>
    unabbrev_all_tac >>
    gs [mkClks_def]) >>
  unabbrev_all_tac >>
  fs [] >>
  ‘EL n (ZIP (REPLICATE (LENGTH zs) x,zs)) =
   (EL n (REPLICATE (LENGTH zs) x), EL n zs)’ by (
    match_mp_tac EL_ZIP >>
    fs []) >>
  gs [shape_of_def]
QED



Theorem foldl_word_size_of:
  ∀xs ys n.
    LENGTH xs = LENGTH ys ⇒
    FOLDL
    (λa e. a +
           size_of_shape (shape_of ((λ(x,y). ValWord (n2w (x − y))) e)))
    n (ZIP (xs,ys)) = n + LENGTH xs
Proof
  Induct >>
  rw [] >>
  cases_on ‘ys’ >> fs [] >>
  fs [panLangTheory.size_of_shape_def, shape_of_def]
QED

Theorem state_rel_intro:
  ∀clks outs s t.
    state_rel clks outs s (t:('a,time_input) panSem$state) ⇒
     equivs t.locals s.location s.waitTime ∧
    ffi_vars t.locals t.base_addr ∧  time_vars t.locals ∧
    mem_config t.memory t.memaddrs t.be t.base_addr ∧
    LENGTH clks ≤ 29 ∧
    defined_clocks s.clocks clks ∧
    let
      ffi = t.ffi.ffi_state;
      io_events = t.ffi.io_events;
      (tm,io_flg) = ffi 0
    in
      t.ffi = build_ffi (:'a) t.be (MAP explode outs) ffi io_events ∧
      input_time_rel ffi ∧
      time_seq ffi (dimword (:'a)) ∧
      FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w tm)) ∧
      clocks_rel s.clocks t.locals clks tm
Proof
  rw [state_rel_def]
QED

Theorem resetClksVals_eq_map:
  ∀tclks fm clks.
    EVERY (λck. MEM ck clks) tclks ∧
    EVERY (λck. ∃n. FLOOKUP fm ck = SOME n) clks ⇒
    resetClksVals fm clks tclks =
    MAP (ValWord ∘ n2w)
        (MAP (λck. if MEM ck tclks then 0 else (THE (FLOOKUP fm ck))) clks)
Proof
  rw [] >>
  fs [resetClksVals_def] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  fs [resetClocks_def] >>
  qmatch_goalsub_abbrev_tac ‘EL _ (MAP ff _)’ >>
  ‘EL n (MAP ff clks) = ff (EL n clks)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘ff’] >>
  cases_on ‘MEM (EL n clks) tclks’ >>
  fs []
  >- (
  ‘FLOOKUP (fm |++ ZIP (tclks,MAP (λx. 0) tclks)) (EL n clks) = SOME 0’ by (
    fs [MEM_EL] >>
    match_mp_tac update_eq_zip_map_flookup >>
    gs []) >>
  fs []) >>
  ‘FLOOKUP (fm |++ ZIP (tclks,MAP (λx. 0) tclks)) (EL n clks) =
   FLOOKUP fm (EL n clks) ’ by (
    match_mp_tac flookup_fupdate_zip_not_mem >>
    fs []) >>
  fs []
QED


Triviality one_leq_suc:
  ∀n. 1 ≤ SUC n
Proof
  Induct >>
  fs []
QED

Triviality lt_less_one:
  n < m - 1 ⇒ n < (m:num)
Proof
  rw [] >>
  fs []
QED

Theorem mod_greater_neq1:
  d + st = (st + wt) MOD (k:num) ∧
  wt < k ∧ d < wt ∧
  k < st + wt ⇒ F
Proof
  CCONTR_TAC >> fs [] >>
  ‘0 < k’ by fs [] >>
  ‘d + st < k’ by metis_tac [MOD_LESS] >>
  ‘((st + wt) - k) MOD k = (st + wt) MOD k’ by (irule SUB_MOD >> fs []) >>
  pop_assum (fs o single o GSYM)
QED


Theorem eval_wait_not_zero':
  !(t:('a,'b) panSem$state).
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «waitSet» = SOME (ValWord 0w) ∧
    (?tm. FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w tm)) ∧
          ?wt st.
            FLOOKUP t.locals «wakeUpAt» = SOME (ValWord (n2w (st + wt))) ∧
            tm < st + wt ∧  st ≤ tm ∧
            wt < dimword (:α) ∧
            tm < dimword (:α) ∧
            st < dimword (:α)) ==>
    ?w.
      eval t wait = SOME (ValWord w) ∧
      w ≠ 0w
Proof
  rw [] >>
  ‘∃d. tm = d + st’ by (
    gs [LESS_OR_EQ]
    >-  metis_tac [LESS_ADD] >>
    qexists_tac ‘0’ >> gs []) >>
  gvs [] >>
  fs [wait_def] >>
  fs [eval_def, OPT_MMAP_def] >>
  gs [active_low_def,
      wordLangTheory.word_op_def] >>
  TOP_CASE_TAC >>
  fs [] >>
  fs [asmTheory.word_cmp_def] >>
  fs [addressTheory.WORD_CMP_NORMALISE] >>
  fs [word_ls_n2w] >>
  ‘wt MOD dimword (:α) = wt’ by (
    match_mp_tac LESS_MOD >> fs []) >>
  ‘st MOD dimword (:α) = st’ by (
    match_mp_tac LESS_MOD >> fs []) >>
  fs [] >> rveq >> gs [] >>
  cases_on ‘st + wt < dimword (:α)’
  >- (
    ‘(st + wt) MOD dimword (:α) = st + wt’ by (
      match_mp_tac LESS_MOD >> fs []) >>
    gs []) >>
  gs [NOT_LESS] >>
  gs [LESS_OR_EQ] >>
  metis_tac [mod_greater_neq1]
QED

Theorem step_input:
  !prog i m n s s' (t:('a,time_input) panSem$state) ist.
    step prog (LAction (Input i)) m n s s' ∧
    m = dimword (:α) - 1 ∧
    n = FST (t.ffi.ffi_state 0) ∧
    FST (t.ffi.ffi_state 1) < dimword (:α) - 2 ∧
    ~MEM "get_time_input" (MAP explode (out_signals prog)) ∧
    state_rel (clksOf prog) (out_signals prog) s t ∧
    wakeup_shape t.locals s.waitTime ist ∧
    input_stime_rel s.waitTime ist (FST (t.ffi.ffi_state 0)) ∧
    (* wait_time_locals (:α) t.locals s.waitTime t.ffi.ffi_state ∧ *)
    (* wait_time_locals (:α) t.locals s.waitTime t.ffi.ffi_state ∧ *)
    well_formed_terms prog s.location t.code ∧
    code_installed t.code prog ∧
    (* we can update the input_rel to take t.ffi.ffi_state, but this
    is also fine *)
    input_rel t.locals i (next_ffi t.ffi.ffi_state) ∧
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    mem_read_ffi_results (:α) t.ffi.ffi_state 1 ∧
    task_ret_defined t.locals (nClks prog) ∧
    good_dimindex (:'a) ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      (NONE, t') ∧
      code_installed t'.code prog ∧
      state_rel (clksOf prog) (out_signals prog) s' t' ∧
      t'.ffi.ffi_state = next_ffi t.ffi.ffi_state ∧
      t'.ffi.oracle = t.ffi.oracle ∧
      t'.code = t.code ∧
      t'.be = t.be ∧ t'.base_addr = t.base_addr ∧
      t'.eshapes = t.eshapes ∧
      FLOOKUP t'.locals «sysTime» = FLOOKUP t.locals «sysTime» ∧
      FLOOKUP t'.locals «event»   = SOME (ValWord 0w) ∧
      FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
      task_ret_defined t'.locals (nClks prog) ∧
      input_io_events_rel i t t' ∧
      FLOOKUP t'.locals «wakeUpAt» =
        SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) +
          case s'.waitTime of
          | NONE => 0
          | SOME wt => wt))) ∧
      FLOOKUP t'.locals «waitSet» =
        SOME (ValWord (n2w (
          case s'.waitTime of
          | NONE => 1
          | _ => 0))) ∧
      (case s'.waitTime of
       | SOME wt => wt < dimword (:α)
       | _ => T)

Proof
  rw [] >>
  fs [task_controller_def] >>
  fs [panLangTheory.nested_seq_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  qexists_tac ‘2’ >>
  pairarg_tac >> rgs [] >>
  pop_assum mp_tac >>
  fs [wait_input_time_limit_def] >>
  rewrite_tac [Once evaluate_def] >>
  ‘∃w. eval t wait = SOME (ValWord w) ∧ w ≠ 0w’ by (
    cases_on ‘s.waitTime’
    >- (
      rgs [state_rel_def, equivs_def, active_low_def] >>
      match_mp_tac step_delay_eval_wait_not_zero >>
      rgs [state_rel_def, equivs_def, time_vars_def, active_low_def]) >>
    ‘x ≠ 0’ by rgs [step_cases] >>
    match_mp_tac eval_wait_not_zero' >>
    rgs [input_rel_def, next_ffi_def] >>
    conj_tac
    >- rgs [state_rel_def, equivs_def, active_low_def, time_vars_def] >>
    qexists_tac ‘FST (t.ffi.ffi_state 1)’ >>
    rgs [] >>
    gvs [wakeup_shape_def, input_stime_rel_def] >>
    qexists_tac ‘wt'’ >>
    qexists_tac ‘ist’ >>
    rgs [input_rel_def, next_ffi_def] >>
    rgs [state_rel_def] >>
    pairarg_tac >> rgs [] >> rgs [] >>
    ‘FST (t.ffi.ffi_state 1) = FST (t.ffi.ffi_state 0)’ by (
      rgs [input_time_rel_def] >>
      last_x_assum (qspec_then ‘0’ mp_tac) >>
      rgs [input_time_eq_def, has_input_def]) >>
    gvs [step_cases]) >>
  rgs [eval_upd_clock_eq] >>
  rgs [dec_clock_def] >>
  (* evaluating the function *)
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once check_input_time_def] >>
  fs [panLangTheory.nested_seq_def] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  drule state_rel_imp_mem_config >>
  rewrite_tac [Once mem_config_def] >>
  strip_tac >>
  fs [] >>
  ‘∃bytes.
     read_bytearray t.base_addr (w2n (ffiBufferSize:'a word))
                    (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes’ by (
    gs[state_rel_def]>>
    match_mp_tac read_bytearray_some_bytes_for_ffi >>
    rgs []) >>
  drule evaluate_ext_call >>
  disch_then (qspecl_then [‘MAP explode (out_signals prog)’, ‘bytes’] mp_tac) >>
  impl_tac
  >- (
    rgs [state_rel_def] >>
    pairarg_tac >> rgs []) >>
  strip_tac >> rgs [] >>
  rveq >> rgs [] >>
  drule state_rel_imp_ffi_vars >>
  strip_tac >>
  pop_assum mp_tac >>
  rewrite_tac [Once ffi_vars_def] >>
  strip_tac >>
  drule state_rel_imp_systime_defined >>
  strip_tac >>
  (* reading systime *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
  ‘nt.memory t.base_addr = Word (n2w (FST(t.ffi.ffi_state 1)))’ by (
    fs [Abbr ‘nt’] >>
    qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
    rgs [mem_read_ffi_results_def] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
    last_x_assum
    (qspecl_then
     [‘t with clock := t.clock + 1’,
      ‘ft’] mp_tac) >>
    impl_tac
    >- rgs [Abbr ‘ft’, nexts_ffi_def, GSYM ETA_AX] >>
    strip_tac >>
    rgs [Abbr ‘ft’, nexts_ffi_def]) >>
  drule evaluate_assign_load >>
  rgs [] >>
  disch_then (qspecl_then
              [‘t.base_addr’, ‘tm’,
               ‘n2w (FST (t.ffi.ffi_state 1))’] mp_tac) >>
  impl_tac
  >- (
    rgs [Abbr ‘nt’] >>
    fs [state_rel_def]) >>
  strip_tac >> fs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  (* reading input to the variable event *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «event» _, nnt)’ >>
  ‘nnt.memory (t.base_addr +  bytes_in_word) =
   Word (n2w (SND(t.ffi.ffi_state 1)))’ by (
    fs [Abbr ‘nnt’, Abbr ‘nt’] >>
    qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
    rgs [mem_read_ffi_results_def] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
    last_x_assum (qspecl_then [‘t with clock := t.clock + 1’, ‘ft’] mp_tac) >>
    impl_tac
    >- rgs [Abbr ‘ft’, nexts_ffi_def, GSYM ETA_AX] >>
    strip_tac >>
    rgs [Abbr ‘ft’, nexts_ffi_def, GSYM ETA_AX]) >>
  rgs [] >>
  drule evaluate_assign_load_next_address >>
  rgs [] >>
  disch_then (qspecl_then
              [‘t.base_addr’,
               ‘n2w (SND (nexts_ffi 0 t.ffi.ffi_state 1))’] mp_tac) >>
  impl_tac
  >- (
    rgs [Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
    rgs [state_rel_def, time_vars_def, FLOOKUP_UPDATE,
        nexts_ffi_def, mem_config_def]) >>
  strip_tac >>
  rveq >> rgs [] >>
  (* isInput *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «isInput» _, nnnt)’ >>
  ‘nnnt.memory (t.base_addr +  bytes_in_word) =
   Word (n2w (SND(t.ffi.ffi_state 1)))’ by fs [Abbr ‘nnnt’] >>
  rgs [] >>
  ‘nnnt.memory (t.base_addr +  bytes_in_word) ≠ Word 0w’ by (
    rgs [input_rel_def, nexts_ffi_def, next_ffi_def] >>
    rgs [step_cases] >>
    drule pick_term_dest_eq >>
    strip_tac >>
    pop_assum mp_tac >>
    disch_then (qspec_then ‘SND (t.ffi.ffi_state 1) − 1’ mp_tac) >>
    impl_tac >- fs [] >>
    strip_tac >>
    ‘SND (t.ffi.ffi_state 1) − 1 + 1 = SND (t.ffi.ffi_state 1)’ by (
      match_mp_tac SUB_ADD >>
      cases_on ‘SND (t.ffi.ffi_state 1)’
      >- metis_tac [] >>
      metis_tac [one_leq_suc]) >>
    ‘SND (t.ffi.ffi_state 1) MOD dimword (:α) =
     SND (t.ffi.ffi_state 1)’ suffices_by metis_tac [] >>
    match_mp_tac LESS_MOD >>
    match_mp_tac lt_less_one >>
    metis_tac []) >>
  fs [] >>
  drule evaluate_assign_compare_next_address_uneq >>
  rgs [] >>
  disch_then (qspecl_then [‘t.base_addr’,
                           ‘n2w (SND (t.ffi.ffi_state 1))’] mp_tac) >>
  impl_tac
  >- (
    rgs [Abbr ‘nnnt’, Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
    rgs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
    rgs [nexts_ffi_def, mem_config_def]) >>
  strip_tac >>
  rgs [] >> rveq >> rgs [] >>
  (* If statement *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  drule evaluate_if_compare_sys_time >>
  disch_then (qspec_then ‘FST (t.ffi.ffi_state 1)’ mp_tac) >>
  impl_tac
  >- (
    unabbrev_all_tac >>
    rgs [FLOOKUP_UPDATE, nexts_ffi_def] >>
    rgs [step_cases, ADD1, state_rel_def, input_time_rel_def] >>
    pairarg_tac >> rgs [] >>
    last_x_assum (qspec_then ‘0’ mp_tac) >>
    rgs [input_time_eq_def, has_input_def, input_rel_def, next_ffi_def] >>
    strip_tac >>
    drule LESS_MOD >>
    strip_tac >> rgs []) >>
  strip_tac >> rveq >> rgs [] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  strip_tac >> fs [] >>
  rveq >> rgs [] >>
  strip_tac >>
  (* loop should break now *)
  fs [step_cases] >>
  rgs [input_rel_def] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  fs [wait_input_time_limit_def] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  ‘FLOOKUP (nnnt with locals := nnnt.locals |+ («isInput» ,ValWord 0w)).locals
   «isInput» = SOME (ValWord 0w)’ by fs [FLOOKUP_UPDATE] >>
  drule step_input_eval_wait_zero >>
  impl_tac
  >- (
    unabbrev_all_tac >> rgs [] >>
    fs [FLOOKUP_UPDATE] >>
    rgs [state_rel_def, time_vars_def]) >>
  rgs [eval_upd_clock_eq] >>
  strip_tac >>
  strip_tac >>
  unabbrev_all_tac >>
  rveq >> rgs [] >>
  (* the new If statement *)
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, nnt)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> rgs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  unabbrev_all_tac >>
  gvs [eval_def, FLOOKUP_UPDATE, asmTheory.word_cmp_def] >>
  rewrite_tac [Once evaluate_def] >>
  gvs [] >>
  strip_tac >> gvs [] >>
  (* until here *)
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, nnt)’ >>
  ‘FLOOKUP nnt.locals «loc» = FLOOKUP t.locals «loc»’ by
    fs [Abbr ‘nnt’, FLOOKUP_UPDATE] >>
  ‘nnt.code = t.code’ by
    fs [Abbr ‘nnt’, state_component_equality] >>
  ‘FST (t.ffi.ffi_state 1) = FST (t.ffi.ffi_state 0)’ by (
    rgs [state_rel_def] >>
    pairarg_tac >>
    rgs [input_time_rel_def, input_time_eq_def] >>
    last_x_assum (qspec_then ‘0’ mp_tac) >>
    impl_tac
    >- rgs [has_input_def, next_ffi_def] >>
    rgs []) >>
  ‘FLOOKUP nnt.locals «clks» = FLOOKUP t.locals «clks»’ by
    fs [Abbr ‘nnt’, FLOOKUP_UPDATE] >>
  (* calling the function *)
  (* location will come from equivs: state_rel *)
  imp_res_tac state_rel_imp_equivs >>
  fs [equivs_def] >>
  qmatch_asmsub_abbrev_tac
  ‘FLOOKUP _ «loc» = SOME (ValLabel loc)’ >>
  ‘FLOOKUP t.code loc =
   SOME
   ([(«clks» ,genShape (LENGTH (clksOf prog))); («event» ,One)],
    compTerms (clksOf prog) «clks» «event» tms)’ by (
    fs [code_installed_def] >>
    drule ALOOKUP_MEM >>
    strip_tac >>
    last_x_assum drule >>
    strip_tac >>
    fs [Abbr ‘loc’]) >>
  (* evaluation *)
  fs [Once evaluate_def] >>
  pairarg_tac >>
  fs [] >>
  fs [Once evaluate_def, eval_upd_clock_eq] >>
  rgs [Once eval_def, eval_upd_clock_eq, FLOOKUP_UPDATE] >>
  ‘FLOOKUP nnt.locals «sysTime» = SOME (ValWord (n2w (FST (t.ffi.ffi_state 0))))’ by
    rgs [Abbr ‘nnt’, FLOOKUP_UPDATE] >>
  drule eval_normalisedClks >>
  rgs [Abbr ‘nnt’,  FLOOKUP_UPDATE] >>
  qpat_x_assum ‘state_rel (clksOf prog) (out_signals prog) s t’ assume_tac >>
  drule state_rel_intro >>
  strip_tac >> rgs [] >>
  pairarg_tac >> rgs [] >>
  rgs [clocks_rel_def] >>
  disch_then (qspec_then ‘ns’ mp_tac) >>
  impl_tac
  >- (
    conj_tac
    >- rgs [EVERY_MEM, time_seq_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    rgs [clkvals_rel_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    fs [MEM_EL] >>
    first_x_assum (qspec_then ‘n'’ mp_tac) >>
    fs [] >>
    strip_tac >>
    ‘(EL n' (ZIP (clksOf prog,ns))) =
     (EL n' (clksOf prog),EL n' ns)’ by (
      match_mp_tac EL_ZIP >>
      rgs []) >>
    fs []) >>
  strip_tac >>
  fs [] >>
  fs [OPT_MMAP_def] >>
  fs [Once eval_def] >>
  qmatch_asmsub_abbrev_tac ‘(eval nnt)’ >>
  ‘(λa. eval nnt a) =
   eval nnt’ by metis_tac [ETA_AX] >>
  fs [] >>
  fs [timeLangTheory.nClks_def] >>
  ‘LENGTH (clksOf prog) = LENGTH ns’ by rgs [] >>
  rgs [] >>
  (* event eval *)
  rgs [Abbr ‘nnt’, eval_def, FLOOKUP_UPDATE, nexts_ffi_def] >>
  rgs [lookup_code_def] >>
  fs [timeLangTheory.nClks_def] >>
  ‘LENGTH (clksOf prog) = LENGTH ns’ by rgs [] >>
  drule (INST_TYPE
         [``:'a``|->``:'mlstring``,
          ``:'b``|->``:'a``] genshape_eq_shape_of) >>
  disch_then (qspec_then ‘tm’ assume_tac) >>
  rfs [] >>
  fs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  fs [shape_of_def] >>
  fs [dec_clock_def] >>
  pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘(«clks» ,Struct nclks)’ >>
  qmatch_asmsub_abbrev_tac ‘evaluate (_, nnt)’ >>
  rgs [next_ffi_def] >>
  drule  (INST_TYPE [``:'a``|->``:'a``,
                     ``:'b``|->``:time_input``] pick_term_thm) >>
  fs [] >>
  disch_then (qspecl_then [‘nnt’, ‘clksOf prog’,
                           ‘nclks’] mp_tac) >>
  impl_tac
  >- (
    rgs [Abbr ‘nnt’] >>
    res_tac >> rgs [] >> rveq >>
    rgs [well_formed_terms_def] >>
    conj_tac
    >- (
      match_mp_tac mem_to_flookup >>
      fs []) >>
    conj_tac
    >- rgs [resetOutput_def, defined_clocks_def] >>
    conj_tac
    >- (
      fs [resetOutput_def, Abbr ‘nclks’] >>
      rgs [clkvals_rel_def, equiv_val_def] >>
      fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >>
      first_x_assum (qspec_then ‘n’ mp_tac) >>
      fs [] >>
      strip_tac >>
      qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,_))’ >>
      ‘EL n (ZIP (xs,ns)) = (EL n xs, EL n ns)’ by (
      match_mp_tac EL_ZIP >>
      unabbrev_all_tac >>
      fs []) >>
      fs [Abbr ‘xs’] >>
      ‘EL n (REPLICATE (LENGTH ns) (FST (t.ffi.ffi_state 1))) = FST (t.ffi.ffi_state 1)’ by (
      match_mp_tac EL_REPLICATE >>
      fs []) >>
      fs [] >>
      ‘EL n (ZIP (clksOf prog,ns)) = (EL n (clksOf prog), EL n ns)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs []) >>
    conj_tac
    >- (
      rgs [Abbr ‘nclks’, defined_clocks_def, maxClksSize_def] >>
      fs [MAP_MAP_o] >>
      fs [SUM_MAP_FOLDL] >>
      ‘LENGTH (REPLICATE (LENGTH ns) (FST (t.ffi.ffi_state 1))) = LENGTH ns’ by fs [] >>
      drule foldl_word_size_of >>
      disch_then (qspec_then ‘0’ mp_tac) >>
      fs []) >>
    rgs [resetOutput_def] >>
    rgs [out_signals_ffi_def, well_behaved_ffi_def] >>
    rgs [EVERY_MEM] >>
    gen_tac >>
    strip_tac >>
    rgs [] >>
    conj_tac
    >- rgs [mlintTheory.num_to_str_thm] >>
    conj_tac
    >- rgs [ffiBufferSize_def, bytes_in_word_def,
           good_dimindex_def] >>
    rgs [mem_call_ffi_def, ffi_call_ffi_def] >>
    qmatch_goalsub_abbrev_tac ‘mem_load_byte mm _ _’ >>
    ‘∃bytes.
       read_bytearray t.base_addr (w2n (ffiBufferSize:'a word))
                      (mem_load_byte mm t.memaddrs t.be) = SOME bytes’ by (
      match_mp_tac read_bytearray_some_bytes_for_ffi >>
      rgs [state_rel_def, mem_config_def]) >>
    qexists_tac ‘bytes'’ >> rgs [] >>
    rgs [next_ffi_def, build_ffi_def] >>
    rgs [ffiTheory.ffi_state_component_equality] >>
    ‘MEM tms (MAP SND prog)’ by (
      drule ALOOKUP_MEM >>
      rgs [MEM_MAP] >>
      strip_tac >>
      qexists_tac ‘(s.location,tms)’ >>
      rgs []) >>
    ‘MEM (explode (toString out)) (MAP explode (out_signals prog))’ by (
      rgs [timeLangTheory.out_signals_def] >>
      rgs [MEM_MAP] >>
      qexists_tac ‘out’ >> rgs [] >>
      match_mp_tac terms_out_signals_prog >>
      qexists_tac ‘tms’ >>
      rgs [MEM_MAP] >>
      metis_tac []) >>
    cases_on ‘explode (num_to_str out) = "get_time_input"’ >>
    rgs []) >>
  impl_tac
  >- (
    fs [Abbr ‘nnt’] >>
    conj_tac
    >- (
      drule pick_term_dest_eq >>
      strip_tac >>
      pop_assum mp_tac >>
      disch_then (qspec_then ‘SND (t.ffi.ffi_state 1) − 1’ mp_tac) >>
      impl_tac >- fs [] >>
      strip_tac >>
      ‘SND (t.ffi.ffi_state 1) − 1 + 1 < dimword (:α)’ by (
        match_mp_tac lt_less_one >>
        metis_tac []) >>
      ‘1 ≤ SND (t.ffi.ffi_state 1)’ by (
        cases_on ‘SND (t.ffi.ffi_state 1)’
        >- metis_tac [] >>
        metis_tac [one_leq_suc]) >>
      drule SUB_ADD >>
      strip_tac >>
      metis_tac []) >>
    (* from pick_term theorem  *)
    match_mp_tac mem_to_flookup >>
    fs []) >>
  strip_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac
  ‘is_valid_value rt _ rtv’ >>
  ‘is_valid_value rt «taskRet» rtv’ by (
    fs [Abbr ‘rt’, Abbr ‘rtv’] >>
    fs [retVal_def] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    rgs [task_ret_defined_def] >>
    fs [shape_of_def] >>
    rgs [EVERY_MEM] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, resetClksVals_def] >>
    rw [] >>
    fs [MEM_EL] >>
    last_x_assum (qspec_then ‘EL n vs’ mp_tac) >>
    fs [] >>
    impl_tac
    >- metis_tac [] >>
    strip_tac >>
    fs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, shape_of_def]) >>
  fs [] >>
  rgs [panSemTheory.set_var_def] >>
  rveq >> rgs [] >>
  (* from here *)
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [Abbr ‘rt’, Abbr ‘rtv’] >>
  fs [retVal_def] >>
  fs [eval_def, FLOOKUP_UPDATE] >>
  fs [] >>
  qmatch_goalsub_abbrev_tac
    ‘is_valid_value rt _ rtv’ >>
  ‘is_valid_value rt «clks» rtv’ by (
    fs [Abbr ‘rt’, Abbr ‘rtv’] >>
    fs [retVal_def] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [shape_of_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, resetClksVals_def] >>
    rw [] >>
    rgs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, shape_of_def] >>
    ‘EL n (MAP ((λw. ValWord w) ∘ n2w) ns) =
     ((λw. ValWord w) ∘ n2w) (EL n ns)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [shape_of_def]) >>
  fs [] >>
  strip_tac >> rveq >> rgs [] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [eval_def] >>
  qmatch_goalsub_abbrev_tac ‘eval fnt’ >>
  ‘FLOOKUP fnt.locals «sysTime» = SOME (ValWord (n2w (FST (t.ffi.ffi_state 1))))’ by (
    unabbrev_all_tac >>
    fs [FLOOKUP_UPDATE]) >>
  ‘(λa. eval fnt a) =
   eval fnt’ by metis_tac [ETA_AX] >>
  fs [] >>
  pop_assum kall_tac >>
  ‘FLOOKUP fnt.locals «clks» =
   SOME (Struct (MAP ((λw. ValWord w) ∘ n2w)
                 (MAP (λck.
                        if MEM ck tclks then 0 else THE (FLOOKUP s.clocks ck)) (clksOf prog))))’ by (
    fs [Abbr ‘fnt’, FLOOKUP_UPDATE] >>
    fs [Abbr ‘rtv’] >>
    rgs [resetOutput_def] >>
    match_mp_tac resetClksVals_eq_map >>
    conj_tac
    >- (
      rgs [well_formed_terms_def, EVERY_MEM, terms_valid_clocks_def] >>
      rw [] >>
      last_x_assum drule >>
      rgs [valid_clks_def, timeLangTheory.termClks_def, EVERY_MEM]) >>
    rgs [state_rel_def, defined_clocks_def, EVERY_MEM] >>
    rw [] >> res_tac >> rgs []) >>
  ‘EVERY (λn. n ≤ FST (t.ffi.ffi_state 1))
   (MAP (λck.
          if MEM ck tclks then 0 else THE (FLOOKUP s.clocks  ck)) (clksOf prog))’ by (
    rgs [EVERY_MAP, EVERY_MEM] >>
    rw [] >>
    rgs [state_rel_def, clock_bound_def, EVERY_MEM] >>
    rw [] >> res_tac >> rgs [] >>
    rgs [clkvals_rel_def, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EVERY_MEM] >>
    first_x_assum (qspec_then ‘ck’ assume_tac) >>
    rgs []) >>
  drule_all eval_normalisedClks >>
  strip_tac >>
  rgs [] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac
  ‘is_valid_value rrt _ rrtv’ >>
  ‘is_valid_value rrt «clks» rrtv’ by (
    fs [Abbr ‘rrt’,Abbr ‘rrtv’,  Abbr ‘rt’, Abbr ‘rtv’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [shape_of_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, resetClksVals_def] >>
    rw [] >>
    rgs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, shape_of_def, Abbr ‘xs’] >>
    qmatch_goalsub_abbrev_tac ‘ZIP (xs,ys)’ >>
    ‘EL n (ZIP (xs,ys)) =
     (EL n xs,EL n ys)’ by (
      match_mp_tac EL_ZIP >>
      fs [Abbr ‘xs’, Abbr ‘ys’]) >>
    fs [Abbr ‘xs’, Abbr ‘ys’] >>
    fs [shape_of_def] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, Abbr ‘xs’, shape_of_def]) >>
  fs [] >>
  strip_tac >> rgs [] >> rveq >> rgs [] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [Abbr ‘rt’, eval_def, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac
  ‘is_valid_value wvt _ hm’ >>
  ‘is_valid_value wvt «waitSet» hm’ by (
    fs [Abbr ‘wvt’,Abbr ‘hm’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [shape_of_def]) >>
  fs [Abbr ‘wvt’,Abbr ‘hm’] >>
  strip_tac >>
  rgs [] >> rveq >> rgs [] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [eval_def, FLOOKUP_UPDATE, OPT_MMAP_def,
      wordLangTheory.word_op_def] >>
  fs [is_valid_value_def, FLOOKUP_UPDATE, shape_of_def] >>
  strip_tac >>
  rgs [] >> rveq >> rgs [] >>
  drule state_rel_imp_time_vars >>
  rgs [time_vars_def, shape_of_def] >> rveq >> rgs [] >>
  fs [Abbr ‘q’] >>
  fs [evaluate_def] >>
  fs [eval_def, FLOOKUP_UPDATE] >>
  fs [is_valid_value_def, FLOOKUP_UPDATE, shape_of_def] >>
  (* evaluation  completed *)
  conj_tac
  >- (unabbrev_all_tac >> rgs [] >> rveq >> rgs []) >>
  conj_tac
  >- (
    rw [state_rel_def]
    >- (
      rgs [equivs_def, FLOOKUP_UPDATE] >>
      drule pick_term_dest_eq >>
      strip_tac >>
      pop_assum mp_tac >>
      disch_then (qspec_then ‘SND (t.ffi.ffi_state 1) − 1’ mp_tac) >>
      impl_tac >- fs [] >>
      strip_tac >>
      pop_assum mp_tac >>
      disch_then drule >>
      rgs [] >>
      strip_tac >>
      TOP_CASE_TAC >> rgs [active_low_def])
    >- (rgs [ffi_vars_def, FLOOKUP_UPDATE, Abbr ‘nnt’])
    >- rgs [time_vars_def, FLOOKUP_UPDATE]
    >- (
      unabbrev_all_tac >>
      rgs [mem_config_def] >>
      fs[mem_call_ffi_def])
    >- (
      unabbrev_all_tac >>
      rgs [state_rel_def])
   >- (
      rgs [defined_clocks_def] >>
      fs [EVERY_MEM] >>
      rw [] >>
      rgs [state_rel_def, defined_clocks_def] >>
      last_x_assum drule >>
      fs [] >>
      strip_tac >>
      imp_res_tac eval_term_clocks_reset >>
      rgs [resetOutput_def] >>
      res_tac >> rgs []) >>
    pairarg_tac >> rgs [] >> rveq >> rgs [] >>
    rw []
    >- (
      rgs [nffi_state_def, build_ffi_def] >>
      fs [Abbr ‘nnt’, ffi_call_ffi_def] >>
      rgs [ffiTheory.ffi_state_component_equality])
    >- (
      rgs [Abbr ‘nnt’, input_time_rel_def,
        ffi_call_ffi_def, next_ffi_def, input_time_eq_def] >>
      rw [] >>
      first_x_assum (qspec_then ‘n+1’ mp_tac) >>
      rgs [])
    >- (
      rgs [time_seq_def, nffi_state_def, ffi_call_ffi_def,
          Abbr ‘nnt’, next_ffi_def] >>
      rw [] >>
      first_x_assum (qspec_then ‘n+1’ assume_tac) >>
      metis_tac [ADD])
    >- (
      rgs [Abbr ‘nnt’, FLOOKUP_UPDATE, nffi_state_def] >>
      rgs [ffi_call_ffi_def, next_ffi_def]) >>
    rgs [clocks_rel_def, FLOOKUP_UPDATE, nffi_state_def] >>
    fs [Abbr ‘rrtv’] >>
    fs [nffi_state_def, Abbr ‘nnt’, ffi_call_ffi_def, next_ffi_def] >>
    qexists_tac ‘MAP (λck. tm - THE (FLOOKUP s'.clocks ck)) (clksOf prog)’ >>
    rgs [] >>
    conj_tac
    >- (
      rgs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >> rgs [] >>
      qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,ys))’ >>
      ‘EL n (ZIP (xs,ys)) = (EL n xs, EL n ys)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs [Abbr ‘xs’] >>
      ‘EL n (REPLICATE (LENGTH ns) tm) = tm’ by (
        match_mp_tac EL_REPLICATE >>
        fs []) >>
      fs [] >>
      fs [Abbr ‘ys’] >>
      qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
      ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
        match_mp_tac EL_MAP >>
        fs [Abbr ‘xs’]) >>
      fs [Abbr ‘ff’, Abbr ‘xs’] >>
      qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
      ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
        match_mp_tac EL_MAP >>
        fs [Abbr ‘xs’]) >>
      fs [Abbr ‘ff’, Abbr ‘xs’] >>
      TOP_CASE_TAC >> rgs []
      >- (
        ‘FLOOKUP s'.clocks (EL n (clksOf prog)) = SOME 0’ by (
        rgs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
        metis_tac [update_eq_zip_map_flookup]) >>
        rgs []) >>
      ‘?x. FLOOKUP s.clocks (EL n (clksOf prog)) = SOME x ∧
           FLOOKUP s'.clocks (EL n (clksOf prog)) = SOME x’ by (
        rgs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
        rgs [defined_clocks_def, EVERY_MEM] >>
        last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
        impl_tac
        >- metis_tac [MEM_EL] >>
        strip_tac >>
        rgs [] >>
        qpat_x_assum ‘_ = SOME n''’ (assume_tac o GSYM) >>
        fs [] >>
        match_mp_tac flookup_fupdate_zip_not_mem >>
        rgs [MEM_EL]) >>
      rgs []) >>
    rgs [clkvals_rel_def] >>
    conj_tac
    >- (
      rgs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >> rgs [] >>
      qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,ys))’ >>
      ‘EL n (ZIP (xs,ys)) = (EL n xs, EL n ys)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs [Abbr ‘xs’, Abbr ‘ys’] >>
      qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
      ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
        match_mp_tac EL_MAP >>
        fs [Abbr ‘xs’]) >>
      fs [Abbr ‘ff’, Abbr ‘xs’] >>
      ‘THE (FLOOKUP s'.clocks (EL n (clksOf prog))) <= tm’ by (
        rgs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
        cases_on ‘MEM (EL n (clksOf prog)) tclks’
        >- (
          fs [MEM_EL] >>
          ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
           (EL n'' tclks) = SOME 0’ by
            metis_tac [update_eq_zip_map_flookup]>>
          fs []) >>
        rgs [defined_clocks_def, EVERY_MEM] >>
        last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
        impl_tac
        >- metis_tac [MEM_EL] >>
        strip_tac >>
        rgs [] >>
        ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
         (EL n (clksOf prog)) = SOME n''’ by (
          qpat_x_assum ‘_ = SOME n''’ (assume_tac o GSYM) >>
          fs [] >>
          match_mp_tac flookup_fupdate_zip_not_mem >>
          rgs [MEM_EL]) >>
        fs [] >>
        last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
        impl_tac >- metis_tac [MEM_EL] >>
        rgs []) >>
      rgs []) >>
    fs [EVERY_MEM] >>
    rw [] >>
    rgs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
    cases_on ‘MEM (EL n (clksOf prog)) tclks’
    >- (
    fs [MEM_EL] >>
    ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
     (EL n'' tclks) = SOME 0’ by
      metis_tac [update_eq_zip_map_flookup]>>
    fs []) >>
    rgs [defined_clocks_def, EVERY_MEM] >>
    last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
    impl_tac
    >- metis_tac [MEM_EL] >>
    strip_tac >>
    rgs [] >>
    ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
     (EL n (clksOf prog)) = SOME n''’ by (
      qpat_x_assum ‘_ = SOME n''’ (assume_tac o GSYM) >>
      fs [] >>
      match_mp_tac flookup_fupdate_zip_not_mem >>
      rgs [MEM_EL]) >>
    fs [] >>
    last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
    impl_tac >- metis_tac [MEM_EL] >>
    rgs []) >>
  fs [nffi_state_def, Abbr ‘nnt’] >>
  rgs [task_ret_defined_def, FLOOKUP_UPDATE, Abbr ‘rtv’, resetOutput_def,
      resetClksVals_def, ffi_call_ffi_def] >>
  fs [next_ffi_def] >>
  fs [EVERY_MAP] >>
  ‘terms_wtimes_ffi_bound (dimword (:α) − 1)
   (s with <|ioAction := NONE; waitTime := NONE|>) tms’ by
    rgs [Once pickTerm_cases] >>
  rgs [terms_wtimes_ffi_bound_def] >>
  rgs [EVERY_MEM] >>
  last_x_assum (qspec_then ‘Tm (Input (SND (t.ffi.ffi_state 1) − 1)) cnds tclks dest wt’ mp_tac) >>
  rgs [timeLangTheory.termClks_def, timeLangTheory.termWaitTimes_def, resetOutput_def] >>
  strip_tac >>
  reverse conj_tac
  >- (
    cases_on ‘wt’ >> rgs []
    >- (
      ‘s'.waitTime = NONE’ by (
      rgs [Once pickTerm_cases] >>
      rveq >> rgs [] >>
      rgs [evalTerm_cases] >> rveq >>
      rgs [calculate_wtime_def, list_min_option_def]) >>
      rgs []) >>
    fs [] >>
    qmatch_goalsub_abbrev_tac ‘n2w (THE (nwt))’ >>
    ‘?t. nwt = SOME t’ by (
      rgs [Abbr ‘nwt’] >>
      rgs [calculate_wtime_def, list_min_option_def] >>
      TOP_CASE_TAC >>
      rgs []) >>
    rgs [] >>
    ‘s'.waitTime = nwt’ by (
      rgs [Abbr ‘nwt’, Once pickTerm_cases] >>
      rveq >> rgs [] >>
      rgs [evalTerm_cases]) >>
    rgs [word_add_n2w]) >>
  rgs [input_io_events_rel_def] >>
  conj_asm1_tac
  >- (
    qexists_tac ‘bytes’ >>
    rgs [mk_ti_event_def, time_input_def] >>
    drule read_bytearray_LENGTH >>
    strip_tac >>
    rgs [ffiBufferSize_def, good_dimindex_def,
        bytes_in_word_def, dimword_def]) >>
  conj_asm1_tac
  >- (
    rgs [from_io_events_def, DROP_LENGTH_APPEND, io_events_dest_def,
        mk_ti_event_def, io_event_dest_def, time_input_def] >>
    qmatch_goalsub_abbrev_tac ‘ZIP (_, nbytes)’ >>
    ‘LENGTH bytes' = LENGTH nbytes’ by (
      fs [Abbr ‘nbytes’, length_get_bytes] >>
      rgs [good_dimindex_def]) >>
    drule MAP_ZIP >>
    rgs [] >>
    strip_tac >>
    ‘words_of_bytes t.be nbytes =
     [n2w(FST (t.ffi.ffi_state 1)); (n2w(SND (t.ffi.ffi_state 1))):'a word]’ by (
      fs [Abbr ‘nbytes’] >>
      match_mp_tac words_of_bytes_get_bytes >>
      rgs []) >>
    rgs [input_eq_ffi_seq_def] >>
    cases_on ‘t.ffi.ffi_state 1’ >> rgs [] >>
    rgs [input_rel_def, step_cases, next_ffi_def] >>
    drule pick_term_dest_eq >>
    simp []) >>
  rgs [from_io_events_def, DROP_LENGTH_APPEND, input_eq_ffi_seq_def] >>
  rgs [DROP_LENGTH_APPEND, decode_io_events_def, io_events_dest_def,
      mk_ti_event_def, decode_io_event_def]  >>
  cases_on ‘t.ffi.ffi_state 1’ >> rgs [] >>
  rgs [to_input_def]
QED


Theorem step_output:
  !prog os m it s s' (t:('a,time_input) panSem$state).
    step prog (LAction (Output os)) m it s s' ∧
    m = dimword (:α) - 1 ∧
    ~MEM "get_time_input" (MAP explode (out_signals prog)) ∧
    it = FST (t.ffi.ffi_state 0) ∧
    FST (t.ffi.ffi_state 0) < dimword (:α) - 2 ∧
    state_rel (clksOf prog) (out_signals prog) s t ∧
    well_formed_terms prog s.location t.code ∧
    code_installed t.code prog ∧
    output_rel t.locals t.ffi.ffi_state ∧
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «event»   = SOME (ValWord 0w) ∧
    task_ret_defined t.locals (nClks prog) ∧
    good_dimindex (:'a) ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      (NONE, t') ∧
      code_installed t'.code prog ∧
      state_rel (clksOf prog) (out_signals prog) s' t' ∧
      t'.ffi.ffi_state = t.ffi.ffi_state ∧
      t'.ffi.oracle = t.ffi.oracle ∧
      t'.code = t.code ∧
      t'.be = t.be ∧ t'.base_addr = t.base_addr ∧
      t'.eshapes = t.eshapes ∧
      FLOOKUP t'.locals «sysTime» = FLOOKUP t.locals «sysTime» ∧
      FLOOKUP t'.locals «event»   = SOME (ValWord 0w) ∧
      FLOOKUP t'.locals «isInput» = SOME (ValWord 1w) ∧
      task_ret_defined t'.locals (nClks prog) ∧
      output_io_events_rel os t t' ∧
      FLOOKUP t'.locals «wakeUpAt» =
      SOME (ValWord (n2w (FST (t.ffi.ffi_state 0) +
         case s'.waitTime of
         | NONE => 0
         | SOME wt => wt))) ∧
      FLOOKUP t'.locals «waitSet» =
        SOME (ValWord (n2w (
          case s'.waitTime of
          | NONE => 1
          | _ => 0))) ∧
      (case s'.waitTime of
       | SOME wt => wt < dimword (:α)
       | _ => T)
Proof
  rw [] >>
  fs [] >>
  fs [step_cases, task_controller_def,
      panLangTheory.nested_seq_def] >>
  ‘FLOOKUP t.locals «waitSet» = SOME (ValWord 0w)’ by
    rgs [state_rel_def, equivs_def, active_low_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  fs [wait_input_time_limit_def] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  qexists_tac ‘1’ >>
  fs [] >>
  rgs [output_rel_def] >>
  drule step_delay_eval_wait_zero >>
  disch_then (qspec_then ‘n2w (nt + wt)’ mp_tac) >>
  rgs [] >>
  strip_tac >>
  rgs [eval_upd_clock_eq] >>
  fs [Abbr ‘q’] >>
  (* the new If statement *)
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, nnt)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> rgs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  unabbrev_all_tac >>
  gvs [eval_def, FLOOKUP_UPDATE, asmTheory.word_cmp_def] >>
  rewrite_tac [Once evaluate_def] >>
  gvs [] >>
  strip_tac >> gvs [] >>
  (* until here *)
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  (* calling the function *)
  (* location will come from equivs: state_rel *)
  imp_res_tac state_rel_imp_equivs >>
  fs [equivs_def] >>
  qmatch_asmsub_abbrev_tac
  ‘FLOOKUP _ «loc» = SOME (ValLabel loc)’ >>
  ‘FLOOKUP t.code loc =
   SOME
   ([(«clks» ,genShape (LENGTH (clksOf prog))); («event» ,One)],
    compTerms (clksOf prog) «clks» «event» tms)’ by (
    fs [code_installed_def] >>
    drule ALOOKUP_MEM >>
    strip_tac >>
    last_x_assum drule >>
    strip_tac >>
    fs [Abbr ‘loc’]) >>
  (* evaluation *)
  fs [Once evaluate_def] >>
  pairarg_tac >>
  fs [] >>
  fs [Once evaluate_def, eval_upd_clock_eq] >>
  rgs [Once eval_def, eval_upd_clock_eq, FLOOKUP_UPDATE] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (eval nnt) [_ ; _]’ >>
  ‘FLOOKUP nnt.locals «sysTime» = SOME (ValWord (n2w (FST (t.ffi.ffi_state 0))))’ by
    fs [Abbr ‘nnt’, FLOOKUP_UPDATE] >>
  drule eval_normalisedClks >>
  rgs [Abbr ‘nnt’,  FLOOKUP_UPDATE] >>
  qpat_x_assum ‘state_rel (clksOf prog) (out_signals prog) s t’ assume_tac >>
  drule state_rel_intro >>
  strip_tac >> rgs [] >>
  pairarg_tac >> rgs [] >>
  rgs [clocks_rel_def] >>
  disch_then (qspec_then ‘ns’ mp_tac) >>
  impl_tac
  >- (
    conj_tac
    >- rgs [EVERY_MEM, time_seq_def, output_rel_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    rgs [clkvals_rel_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    fs [MEM_EL] >>
    first_x_assum (qspec_then ‘n'’ mp_tac) >>
    fs [] >>
    strip_tac >>
    ‘(EL n' (ZIP (clksOf prog,ns))) =
     (EL n' (clksOf prog),EL n' ns)’ by (
      match_mp_tac EL_ZIP >>
      rgs []) >>
    fs []) >>
  strip_tac >>
  fs [] >>
  fs [OPT_MMAP_def] >>
  fs [Once eval_def] >>
  qmatch_asmsub_abbrev_tac ‘(eval nnt)’ >>
  ‘(λa. eval nnt a) =
   eval nnt’ by metis_tac [ETA_AX] >>
  fs [] >>
  fs [timeLangTheory.nClks_def] >>
  ‘LENGTH (clksOf prog) = LENGTH ns’ by rgs [] >>
  rgs [] >>
  (* event eval *)
  rgs [Abbr ‘nnt’, eval_def, FLOOKUP_UPDATE] >>
  rgs [lookup_code_def] >>
  fs [timeLangTheory.nClks_def] >>
  ‘LENGTH (clksOf prog) = LENGTH ns’ by rgs [] >>
  drule (INST_TYPE
         [``:'a``|->``:'mlstring``,
          ``:'b``|->``:'a``] genshape_eq_shape_of) >>
  disch_then (qspec_then ‘nt + wt’ assume_tac) >>
  rfs [] >>
  fs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  fs [shape_of_def] >>
  fs [dec_clock_def] >>
  pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘(«clks» ,Struct nclks)’ >>
  qmatch_asmsub_abbrev_tac ‘evaluate (_, nnt)’ >>
  drule  (INST_TYPE [``:'a``|->``:'a``,
                     ``:'b``|->``:time_input``] pick_term_thm) >>
  fs [] >>
  disch_then (qspecl_then [‘nnt’, ‘clksOf prog’,
                           ‘nclks’] mp_tac) >>
  impl_tac
  >- (
    rgs [Abbr ‘nnt’] >>
    res_tac >> rgs [] >> rveq >>
    rgs [well_formed_terms_def] >>
    conj_tac
    >- (
      match_mp_tac mem_to_flookup >>
      fs []) >>
    conj_tac
    >- rgs [resetOutput_def, defined_clocks_def] >>
    conj_tac
    >- (
      fs [resetOutput_def, Abbr ‘nclks’] >>
      rgs [clkvals_rel_def, equiv_val_def] >>
      fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >>
      first_x_assum (qspec_then ‘n’ mp_tac) >>
      fs [] >>
      strip_tac >>
      qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,_))’ >>
      ‘EL n (ZIP (xs,ns)) = (EL n xs, EL n ns)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs [Abbr ‘xs’] >>
      ‘EL n (REPLICATE (LENGTH ns) (nt + wt)) = nt + wt’ by (
        match_mp_tac EL_REPLICATE >>
        fs []) >>
      fs [] >>
      ‘EL n (ZIP (clksOf prog,ns)) = (EL n (clksOf prog), EL n ns)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs []) >>
    conj_tac
    >- (
      rgs [Abbr ‘nclks’, defined_clocks_def, maxClksSize_def] >>
      fs [MAP_MAP_o] >>
      fs [SUM_MAP_FOLDL] >>
      ‘LENGTH (REPLICATE (LENGTH ns) (nt + wt)) = LENGTH ns’ by fs [] >>
      drule foldl_word_size_of >>
      disch_then (qspec_then ‘0’ mp_tac) >>
      fs []) >>
    rgs [resetOutput_def] >>
    rgs [out_signals_ffi_def, well_behaved_ffi_def] >>
    rgs [EVERY_MEM] >>
    gen_tac >>
    strip_tac >>
    rgs [] >>
    conj_tac
    >- rgs [mlintTheory.num_to_str_thm] >>
    conj_tac
    >- rgs [ffiBufferSize_def, bytes_in_word_def,
           good_dimindex_def] >>
    rgs [mem_call_ffi_def, ffi_call_ffi_def] >>
    qmatch_goalsub_abbrev_tac ‘mem_load_byte mm _ _’ >>
    ‘∃bytes.
       read_bytearray t.base_addr (w2n (ffiBufferSize:'a word))
              (mem_load_byte mm t.memaddrs t.be) = SOME bytes’ by (
      match_mp_tac read_bytearray_some_bytes_for_ffi >>
      rgs [state_rel_def, mem_config_def]) >>
    qexists_tac ‘bytes’ >> rgs [] >>
    rgs [next_ffi_def, build_ffi_def] >>
    rgs [ffiTheory.ffi_state_component_equality] >>
    ‘MEM tms (MAP SND prog)’ by (
      drule ALOOKUP_MEM >>
      rgs [MEM_MAP] >>
      strip_tac >>
      qexists_tac ‘(s.location,tms)’ >>
      rgs []) >>
    ‘MEM (explode (toString out)) (MAP explode (out_signals prog))’ by (
      rgs [timeLangTheory.out_signals_def] >>
      rgs [MEM_MAP] >>
      qexists_tac ‘out’ >> rgs [] >>
      match_mp_tac terms_out_signals_prog >>
      qexists_tac ‘tms’ >>
      rgs [MEM_MAP] >>
      metis_tac []) >>
    cases_on ‘explode (num_to_str out) = "get_time_input"’ >>
    rgs []) >>
  impl_tac
  >- (
    fs [Abbr ‘nnt’] >>
    match_mp_tac mem_to_flookup >>
    fs []) >>
  strip_tac >> fs [] >>
  ‘out = os’ by (
    drule pick_term_dest_eq >>
    rgs [] >>
    strip_tac >>
    pop_assum mp_tac >>
    disch_then drule >>
    rgs []) >>
  rveq >> rgs [] >>
  qmatch_asmsub_abbrev_tac
  ‘is_valid_value rt _ rtv’ >>
  ‘is_valid_value rt «taskRet» rtv’ by (
    fs [Abbr ‘rt’, Abbr ‘rtv’] >>
    fs [retVal_def] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    rgs [task_ret_defined_def] >>
    fs [shape_of_def] >>
    rgs [EVERY_MEM] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, resetClksVals_def] >>
    rw [] >>
    fs [MEM_EL] >>
    last_x_assum (qspec_then ‘EL n vs’ mp_tac) >>
    fs [] >>
    impl_tac
    >- metis_tac [] >>
    strip_tac >>
    fs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, shape_of_def]) >>
  fs [] >>
  rgs [panSemTheory.set_var_def] >>
  rveq >> rgs [] >>
  (* from here *)
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [Abbr ‘rt’, Abbr ‘rtv’] >>
  fs [retVal_def] >>
  fs [eval_def, FLOOKUP_UPDATE] >>
  fs [] >>
  qmatch_goalsub_abbrev_tac
    ‘is_valid_value rt _ rtv’ >>
  ‘is_valid_value rt «clks» rtv’ by (
    fs [Abbr ‘rt’, Abbr ‘rtv’] >>
    fs [retVal_def] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [shape_of_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, resetClksVals_def] >>
    rw [] >>
    rgs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, shape_of_def] >>
    ‘EL n (MAP ((λw. ValWord w) ∘ n2w) ns) =
     ((λw. ValWord w) ∘ n2w) (EL n ns)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [shape_of_def]) >>
  fs [] >>
  strip_tac >> rveq >> rgs [] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [eval_def] >>
  qmatch_goalsub_abbrev_tac ‘eval fnt’ >>
  ‘FLOOKUP fnt.locals «sysTime» = SOME (ValWord (n2w (nt + wt)))’ by (
    unabbrev_all_tac >>
    fs [FLOOKUP_UPDATE]) >>
  ‘(λa. eval fnt a) =
   eval fnt’ by metis_tac [ETA_AX] >>
  fs [] >>
  pop_assum kall_tac >>
  ‘FLOOKUP fnt.locals «clks» =
   SOME (Struct (MAP ((λw. ValWord w) ∘ n2w)
                 (MAP (λck.
                        if MEM ck tclks then 0 else THE (FLOOKUP s.clocks  ck)) (clksOf prog))))’ by (
    fs [Abbr ‘fnt’, FLOOKUP_UPDATE] >>
    fs [Abbr ‘rtv’] >>
    rgs [resetOutput_def] >>
    match_mp_tac resetClksVals_eq_map >>
    conj_tac
    >- (
      rgs [well_formed_terms_def, EVERY_MEM, terms_valid_clocks_def] >>
      rw [] >>
      last_x_assum drule >>
      rgs [valid_clks_def, timeLangTheory.termClks_def, EVERY_MEM]) >>
    rgs [state_rel_def, defined_clocks_def, EVERY_MEM]) >>
  ‘EVERY (λn. n ≤ nt + wt)
   (MAP (λck.
          if MEM ck tclks then 0 else THE (FLOOKUP s.clocks  ck)) (clksOf prog))’ by (
    rgs [EVERY_MAP, EVERY_MEM] >>
    rw [] >>
    rgs [state_rel_def, defined_clocks_def, EVERY_MEM] >>
    rw [] >> res_tac >> rgs [] >>
    rgs [clkvals_rel_def, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EVERY_MEM] >>
    first_x_assum (qspec_then ‘ck’ assume_tac) >>
    rgs []) >>
  drule_all eval_normalisedClks >>
  strip_tac >>
  rgs [] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac
  ‘is_valid_value rrt _ rrtv’ >>
  ‘is_valid_value rrt «clks» rrtv’ by (
    fs [Abbr ‘rrt’,Abbr ‘rrtv’,  Abbr ‘rt’, Abbr ‘rtv’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [shape_of_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, resetClksVals_def] >>
    rw [] >>
    rgs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, shape_of_def, Abbr ‘xs’] >>
    qmatch_goalsub_abbrev_tac ‘ZIP (xs,ys)’ >>
    ‘EL n (ZIP (xs,ys)) =
     (EL n xs,EL n ys)’ by (
      match_mp_tac EL_ZIP >>
      fs [Abbr ‘xs’, Abbr ‘ys’]) >>
    fs [Abbr ‘xs’, Abbr ‘ys’] >>
    fs [shape_of_def] >>
    qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, Abbr ‘xs’, shape_of_def]) >>
  fs [] >>
  strip_tac >> rgs [] >> rveq >> rgs [] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [Abbr ‘rt’, eval_def, FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac
  ‘is_valid_value wvt _ hm’ >>
  ‘is_valid_value wvt «waitSet» hm’ by (
    fs [Abbr ‘wvt’,Abbr ‘hm’] >>
    fs [is_valid_value_def] >>
    fs [FLOOKUP_UPDATE] >>
    fs [shape_of_def]) >>
  fs [Abbr ‘wvt’,Abbr ‘hm’] >>
  strip_tac >>
  rgs [] >> rveq >> rgs [] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [eval_def, FLOOKUP_UPDATE, OPT_MMAP_def,
      wordLangTheory.word_op_def] >>
  fs [is_valid_value_def, FLOOKUP_UPDATE, shape_of_def] >>
  strip_tac >>
  rgs [] >> rveq >> rgs [] >>
  fs [Abbr ‘q’] >>
  fs [evaluate_def] >>
  fs [eval_def, FLOOKUP_UPDATE] >>
  fs [is_valid_value_def, FLOOKUP_UPDATE, shape_of_def] >>
  (* evaluation  completed *)
  conj_tac
  >- (unabbrev_all_tac >> rgs [] >> rveq >> rgs []) >>
  conj_tac
  >- (
    rw [state_rel_def]
    >- (
      rgs [equivs_def, FLOOKUP_UPDATE] >>
      drule pick_term_dest_eq >>
      rgs [] >>
      strip_tac >>
      pop_assum mp_tac >>
      disch_then drule >>
      rgs [] >>
      strip_tac >>
      TOP_CASE_TAC >> rgs [active_low_def])
    >- (rgs [ffi_vars_def, FLOOKUP_UPDATE, Abbr ‘nnt’])
    >- rgs [time_vars_def, FLOOKUP_UPDATE]
    >- (
      qspec_then ‘t.base_addr’ assume_tac byte_aligned_ba_step>>gs[]>>
      unabbrev_all_tac >>
      rgs [mem_config_def] >>
      fs[mem_call_ffi_def] >>
      conj_tac >>
        fs [] >>
        match_mp_tac write_bytearray_update_byte >>
        rgs [good_dimindex_def, byte_align_aligned, bytes_in_word_def,state_rel_def])
    >- (
      unabbrev_all_tac >>
      rgs [state_rel_def])
    >- (
      rgs [defined_clocks_def] >>
      fs [EVERY_MEM] >>
      rw [] >>
      rgs [state_rel_def, defined_clocks_def] >>
      last_x_assum drule >>
      fs [] >>
      strip_tac >>
      imp_res_tac eval_term_clocks_reset >>
      rgs [resetOutput_def] >>
      res_tac >> rgs []) >>
    pairarg_tac >> rgs [] >> rveq >> rgs [] >>
    rw []
    >- (
      rgs [nffi_state_def, build_ffi_def] >>
      fs [Abbr ‘nnt’, ffi_call_ffi_def] >>
      rgs [ffiTheory.ffi_state_component_equality])
    >- (
      rgs [time_seq_def, nffi_state_def, ffi_call_ffi_def,
          Abbr ‘nnt’, next_ffi_def] >>
      rw [] >>
      first_x_assum (qspec_then ‘n+1’ assume_tac) >>
      metis_tac [ADD])
    >- rgs [Abbr ‘nnt’, FLOOKUP_UPDATE, nffi_state_def] >>
    rgs [clocks_rel_def, FLOOKUP_UPDATE, nffi_state_def] >>
    fs [Abbr ‘rrtv’] >>
    fs [nffi_state_def, Abbr ‘nnt’, ffi_call_ffi_def, next_ffi_def] >>
    qexists_tac ‘MAP (λck. (nt + wt) - THE (FLOOKUP s'.clocks ck)) (clksOf prog)’ >>
    rgs [] >>
    conj_tac
    >- (
      rgs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >> rgs [] >>
      qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,ys))’ >>
      ‘EL n (ZIP (xs,ys)) = (EL n xs, EL n ys)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs [Abbr ‘xs’] >>
      ‘EL n (REPLICATE (LENGTH ns) tm) = tm’ by (
        match_mp_tac EL_REPLICATE >>
        fs []) >>
      fs [] >>
      fs [Abbr ‘ys’] >>
      qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
      ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
        match_mp_tac EL_MAP >>
        fs [Abbr ‘xs’]) >>
      fs [Abbr ‘ff’, Abbr ‘xs’] >>
      qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
      ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
        match_mp_tac EL_MAP >>
        fs [Abbr ‘xs’]) >>
      fs [Abbr ‘ff’, Abbr ‘xs’] >>
      TOP_CASE_TAC >> rgs []
      >- (
        ‘FLOOKUP s'.clocks (EL n (clksOf prog)) = SOME 0’ by (
        rgs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
        metis_tac [update_eq_zip_map_flookup]) >>
        rgs [] >>
        ‘EL n (REPLICATE (LENGTH ns) (nt + wt)) = nt + wt’ by (
          match_mp_tac EL_REPLICATE >>
          rgs []) >>
        rgs []) >>
      ‘?x. FLOOKUP s.clocks (EL n (clksOf prog)) = SOME x ∧
           FLOOKUP s'.clocks (EL n (clksOf prog)) = SOME x’ by (
        rgs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
        rgs [defined_clocks_def, EVERY_MEM] >>
        last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
        impl_tac
        >- metis_tac [MEM_EL] >>
        strip_tac >>
        rgs [] >>
        qpat_x_assum ‘_ = SOME n''’ (assume_tac o GSYM) >>
        fs [] >>
        match_mp_tac flookup_fupdate_zip_not_mem >>
        rgs [MEM_EL]) >>
      rgs [] >>
      ‘EL n (REPLICATE (LENGTH ns) (nt + wt)) = nt + wt’ by (
        match_mp_tac EL_REPLICATE >>
        rgs []) >>
      rgs []) >>
    rgs [clkvals_rel_def] >>
    conj_tac
    >- (
      rgs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >> rgs [] >>
      qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,ys))’ >>
      ‘EL n (ZIP (xs,ys)) = (EL n xs, EL n ys)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs [Abbr ‘xs’, Abbr ‘ys’] >>
      qmatch_goalsub_abbrev_tac ‘MAP ff xs’ >>
      ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
        match_mp_tac EL_MAP >>
        fs [Abbr ‘xs’]) >>
      fs [Abbr ‘ff’, Abbr ‘xs’] >>
      ‘THE (FLOOKUP s'.clocks (EL n (clksOf prog))) <= nt + wt’ by (
        rgs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
        cases_on ‘MEM (EL n (clksOf prog)) tclks’
        >- (
          fs [MEM_EL] >>
          ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
           (EL n'' tclks) = SOME 0’ by
            metis_tac [update_eq_zip_map_flookup]>>
          fs []) >>
        rgs [defined_clocks_def, EVERY_MEM] >>
        last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
        impl_tac
        >- metis_tac [MEM_EL] >>
        strip_tac >>
        rgs [] >>
        ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
         (EL n (clksOf prog)) = SOME n''’ by (
          qpat_x_assum ‘_ = SOME n''’ (assume_tac o GSYM) >>
          fs [] >>
          match_mp_tac flookup_fupdate_zip_not_mem >>
          rgs [MEM_EL]) >>
        fs [] >>
        last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
        impl_tac >- metis_tac [MEM_EL] >>
        rgs [] >>
        strip_tac >>
        rgs []) >>
      rgs []) >>
    fs [EVERY_MEM] >>
    rw [] >>
    rgs [evalTerm_cases, resetOutput_def, resetClocks_def, MEM_EL] >>
    cases_on ‘MEM (EL n (clksOf prog)) tclks’
    >- (
    fs [MEM_EL] >>
    ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
     (EL n'' tclks) = SOME 0’ by
      metis_tac [update_eq_zip_map_flookup]>>
    fs []) >>
    rgs [defined_clocks_def, EVERY_MEM] >>
    last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
    impl_tac
    >- metis_tac [MEM_EL] >>
    strip_tac >>
    rgs [] >>
    ‘FLOOKUP (s.clocks |++ ZIP (tclks,MAP (λx. 0) tclks))
     (EL n (clksOf prog)) = SOME n''’ by (
      qpat_x_assum ‘_ = SOME n''’ (assume_tac o GSYM) >>
      fs [] >>
      match_mp_tac flookup_fupdate_zip_not_mem >>
      rgs [MEM_EL]) >>
    fs [] >>
    last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
    impl_tac >- metis_tac [MEM_EL] >>
    rgs []) >>
  fs [nffi_state_def, Abbr ‘nnt’] >>
  rgs [task_ret_defined_def, FLOOKUP_UPDATE, Abbr ‘rtv’, resetOutput_def,
      resetClksVals_def] >>
  fs [EVERY_MAP] >>
  ‘terms_wtimes_ffi_bound (dimword (:α) − 1)
   (s with <|ioAction := NONE; waitTime := NONE|>) tms’ by
    rgs [Once pickTerm_cases] >>
  rgs [terms_wtimes_ffi_bound_def] >>
  rgs [EVERY_MEM] >>
  last_x_assum (qspec_then ‘Tm (Output os) cnds tclks dest wt'’ mp_tac) >>
  rgs [timeLangTheory.termClks_def, timeLangTheory.termWaitTimes_def, resetOutput_def] >>
  strip_tac >>
  reverse conj_tac
  >- (
    cases_on ‘wt'’ >> rgs []
    >- (
      ‘s'.waitTime = NONE’ by (
        rgs [Once pickTerm_cases] >>
        rveq >> rgs [] >>
        rgs [evalTerm_cases] >> rveq >>
        rgs [calculate_wtime_def, list_min_option_def]) >>
      rgs []) >>
    fs [] >>
    qmatch_goalsub_abbrev_tac ‘n2w (THE (nwt))’ >>
    ‘?t. nwt = SOME t’ by (
      rgs [Abbr ‘nwt’] >>
      rgs [calculate_wtime_def, list_min_option_def] >>
      TOP_CASE_TAC >>
      rgs []) >>
    rgs [] >>
    ‘s'.waitTime = nwt’ by (
      rgs [Abbr ‘nwt’, Once pickTerm_cases] >>
      rveq >> rgs [] >>
      rgs [evalTerm_cases]) >>
    rgs [word_add_n2w]) >>
  rgs [output_io_events_rel_def] >>
  conj_tac
  >- metis_tac [] >>
  rgs [DROP_LENGTH_APPEND] >>
  rgs [decode_io_events_def, decode_io_event_def] >>
  ‘explode (toString os) ≠ "get_time_input"’ by (
    rgs [mlintTheory.num_to_str_thm] >>
    assume_tac EVERY_isDigit_num_to_dec_string >>
    pop_assum (qspec_then ‘os’ mp_tac) >>
    rgs [EVERY_MEM] >>
    strip_tac >>
    CCONTR_TAC >>
    rgs [isDigit_def] >>
    qpat_x_assum ‘∀e. _ ⇒ _’ mp_tac >>
    rw [] >>
    qexists_tac ‘#"g"’ >> rgs []) >>
  rgs [mlintTheory.num_to_str_thm, toString_toNum_cancel]
QED


Theorem step_panic_timeout:
  !prog m it s s' (t:('a,time_input) panSem$state).
    step prog (LPanic PanicTimeout) m it s s' ∧
    m = dimword (:α) - 1 ∧
    ~MEM "get_time_input" (MAP explode (out_signals prog)) ∧
    it = FST (t.ffi.ffi_state 0) ∧
    FST (t.ffi.ffi_state 0) < dimword (:α) - 2 ∧
    state_rel (clksOf prog) (out_signals prog) s t ∧
    well_formed_terms prog s.location t.code ∧
    code_installed t.code prog ∧
    output_rel t.locals t.ffi.ffi_state ∧ byte_align t.base_addr = t.base_addr ∧
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.locals «event»   = SOME (ValWord 0w) ∧
    FLOOKUP t.eshapes «panic» = SOME One ∧
    good_dimindex (:'a)  ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      (SOME (Exception «panic» (ValWord 0w)), t') ∧
      code_installed t'.code prog ∧
      t'.ffi.ffi_state = t.ffi.ffi_state ∧
      t'.ffi.io_events = t.ffi.io_events ∧
      t'.ffi.oracle = t.ffi.oracle ∧
      t'.code = t.code ∧
      t'.be = t.be ∧ t'.base_addr = t.base_addr ∧
      t'.eshapes = t.eshapes ∧
      t'.locals = FEMPTY
Proof
  rw [] >>
  fs [] >>
  fs [step_cases, task_controller_def,
      panLangTheory.nested_seq_def] >>
  ‘FLOOKUP t.locals «waitSet» = SOME (ValWord 0w)’ by
    rgs [state_rel_def, equivs_def, active_low_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  fs [wait_input_time_limit_def] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  qexists_tac ‘1’ >>
  fs [] >>
  rgs [output_rel_def] >>
  drule step_delay_eval_wait_zero >>
  disch_then (qspec_then ‘n2w (nt + wt)’ mp_tac) >>
  rgs [] >>
  strip_tac >>
  rgs [eval_upd_clock_eq] >>
  fs [Abbr ‘q’] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, nnt)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  unabbrev_all_tac >>
  gvs [eval_def, FLOOKUP_UPDATE, asmTheory.word_cmp_def] >>
  rewrite_tac [Once evaluate_def] >>
  gvs [] >>
  strip_tac >> gvs [] >>
  (* until here *)
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  (* calling the function *)
  (* location will come from equivs: state_rel *)
  imp_res_tac state_rel_imp_equivs >>
  fs [equivs_def] >>
  qmatch_asmsub_abbrev_tac
  ‘FLOOKUP _ «loc» = SOME (ValLabel loc)’ >>
  ‘FLOOKUP t.code loc =
   SOME
   ([(«clks» ,genShape (LENGTH (clksOf prog))); («event» ,One)],
    compTerms (clksOf prog) «clks» «event» tms)’ by (
    fs [code_installed_def] >>
    drule ALOOKUP_MEM >>
    strip_tac >>
    last_x_assum drule >>
    strip_tac >>
    fs [Abbr ‘loc’]) >>
  (* evaluation *)
  fs [Once evaluate_def] >>
  pairarg_tac >>
  fs [] >>
  fs [Once evaluate_def, eval_upd_clock_eq] >>
  rgs [Once eval_def, eval_upd_clock_eq, FLOOKUP_UPDATE] >>
  qmatch_asmsub_abbrev_tac ‘OPT_MMAP (eval nnt) [_ ; _]’ >>
  ‘FLOOKUP nnt.locals «sysTime» = SOME (ValWord (n2w (FST (t.ffi.ffi_state 0))))’ by
    fs [Abbr ‘nnt’, FLOOKUP_UPDATE] >>
  drule eval_normalisedClks >>
  rgs [Abbr ‘nnt’,  FLOOKUP_UPDATE] >>
  qpat_x_assum ‘state_rel (clksOf prog) (out_signals prog) s t’ assume_tac >>
  drule state_rel_intro >>
  strip_tac >> rgs [] >>
  pairarg_tac >> rgs [] >>
  rgs [clocks_rel_def] >>
  disch_then (qspec_then ‘ns’ mp_tac) >>
  impl_tac
  >- (
    conj_tac
    >- rgs [EVERY_MEM, time_seq_def, output_rel_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    rgs [clkvals_rel_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    fs [MEM_EL] >>
    first_x_assum (qspec_then ‘n'’ mp_tac) >>
    fs [] >>
    strip_tac >>
    ‘(EL n' (ZIP (clksOf prog,ns))) =
     (EL n' (clksOf prog),EL n' ns)’ by (
      match_mp_tac EL_ZIP >>
      rgs []) >>
    fs []) >>
  strip_tac >>
  fs [] >>
  fs [OPT_MMAP_def] >>
  fs [Once eval_def] >>
  qmatch_asmsub_abbrev_tac ‘(eval nnt)’ >>
  ‘(λa. eval nnt a) =
   eval nnt’ by metis_tac [ETA_AX] >>
  fs [] >>
  fs [timeLangTheory.nClks_def] >>
  ‘LENGTH (clksOf prog) = LENGTH ns’ by rgs [] >>
  rgs [] >>
  (* event eval *)
  rgs [Abbr ‘nnt’, eval_def, FLOOKUP_UPDATE] >>
  rgs [lookup_code_def] >>
  fs [timeLangTheory.nClks_def] >>
  ‘LENGTH (clksOf prog) = LENGTH ns’ by rgs [] >>
  drule (INST_TYPE
         [``:'a``|->``:'mlstring``,
          ``:'b``|->``:'a``] genshape_eq_shape_of) >>
  disch_then (qspec_then ‘nt + wt’ assume_tac) >>
  rfs [] >>
  fs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  fs [shape_of_def] >>
  fs [dec_clock_def] >>
  pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘(«clks» ,Struct nclks)’ >>
  qmatch_asmsub_abbrev_tac ‘evaluate (_, nnt)’ >>
  drule  (INST_TYPE [``:'a``|->``:'a``,
                     ``:'b``|->``:time_input``] pick_term_thm) >>
  fs [] >>
  disch_then (qspecl_then [‘nnt’, ‘clksOf prog’,
                           ‘nclks’] mp_tac) >>
  impl_tac
  >- (
    rgs [Abbr ‘nnt’] >>
    res_tac >> rgs [] >> rveq >>
    rgs [well_formed_terms_def] >>
    conj_tac
    >- (
      match_mp_tac mem_to_flookup >>
      fs []) >>
    conj_tac
    >- rgs [resetOutput_def, defined_clocks_def] >>
    conj_tac
    >- (
      fs [resetOutput_def, Abbr ‘nclks’] >>
      rgs [clkvals_rel_def, equiv_val_def] >>
      fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >>
      first_x_assum (qspec_then ‘n’ mp_tac) >>
      fs [] >>
      strip_tac >>
      qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,_))’ >>
      ‘EL n (ZIP (xs,ns)) = (EL n xs, EL n ns)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs [Abbr ‘xs’] >>
      ‘EL n (REPLICATE (LENGTH ns) (nt + wt)) = nt + wt’ by (
        match_mp_tac EL_REPLICATE >>
        fs []) >>
      fs [] >>
      ‘EL n (ZIP (clksOf prog,ns)) = (EL n (clksOf prog), EL n ns)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs []) >>
    conj_tac
    >- (
      rgs [Abbr ‘nclks’, defined_clocks_def, maxClksSize_def] >>
      fs [MAP_MAP_o] >>
      fs [SUM_MAP_FOLDL] >>
      ‘LENGTH (REPLICATE (LENGTH ns) (nt + wt)) = LENGTH ns’ by fs [] >>
      drule foldl_word_size_of >>
      disch_then (qspec_then ‘0’ mp_tac) >>
      fs []) >>
    rgs [resetOutput_def] >>
    rgs [out_signals_ffi_def, well_behaved_ffi_def] >>
    rgs [EVERY_MEM] >>
    gen_tac >>
    strip_tac >>
    rgs [] >>
    conj_tac
    >- rgs [mlintTheory.num_to_str_thm] >>
    conj_tac
    >- rgs [ffiBufferSize_def, bytes_in_word_def,
           good_dimindex_def] >>
    rgs [mem_call_ffi_def, ffi_call_ffi_def] >>
    qmatch_goalsub_abbrev_tac ‘mem_load_byte mm _ _’ >>
    ‘∃bytes.
       read_bytearray t.base_addr (w2n (ffiBufferSize:'a word))
              (mem_load_byte mm t.memaddrs t.be) = SOME bytes’ by (
      match_mp_tac read_bytearray_some_bytes_for_ffi >>
      rgs [state_rel_def, mem_config_def]) >>
    qexists_tac ‘bytes’ >> rgs [] >>
    rgs [next_ffi_def, build_ffi_def] >>
    rgs [ffiTheory.ffi_state_component_equality] >>
    ‘MEM tms (MAP SND prog)’ by (
      drule ALOOKUP_MEM >>
      rgs [MEM_MAP] >>
      strip_tac >>
      qexists_tac ‘(s.location,tms)’ >>
      rgs []) >>
    ‘MEM (explode (toString out)) (MAP explode (out_signals prog))’ by (
      rgs [timeLangTheory.out_signals_def] >>
      rgs [MEM_MAP] >>
      qexists_tac ‘out’ >> rgs [] >>
      match_mp_tac terms_out_signals_prog >>
      qexists_tac ‘tms’ >>
      rgs [MEM_MAP] >>
      metis_tac []) >>
    cases_on ‘explode (num_to_str out) = "get_time_input"’ >>
    rgs []) >>
  impl_tac
  >- (
    fs [Abbr ‘nnt’] >>
    match_mp_tac mem_to_flookup >>
    fs []) >>
  strip_tac >> gvs [] >>
  unabbrev_all_tac >>
  gvs [empty_locals_def]
QED


Theorem step_panic_input:
  !prog i m n s s' (t:('a,time_input) panSem$state) ist.
    step prog (LPanic (PanicInput i)) m n s s' ∧
    m = dimword (:α) - 1 ∧
    n = FST (t.ffi.ffi_state 0) ∧
    FST (t.ffi.ffi_state 1) < dimword (:α) - 2 ∧
    ~MEM "get_time_input" (MAP explode (out_signals prog)) ∧
    state_rel (clksOf prog) (out_signals prog) s t ∧
    wakeup_shape t.locals s.waitTime ist ∧
    input_stime_rel s.waitTime ist (FST (t.ffi.ffi_state 0)) ∧
    well_formed_terms prog s.location t.code ∧
    code_installed t.code prog ∧
    input_rel t.locals i (next_ffi t.ffi.ffi_state) ∧
    FLOOKUP t.locals «isInput» = SOME (ValWord 1w) ∧
    FLOOKUP t.eshapes «panic» = SOME One ∧
    mem_read_ffi_results (:α) t.ffi.ffi_state 1 ∧
    good_dimindex (:'a) ∧ byte_align t.base_addr = t.base_addr ⇒
    ?ck t'.
      evaluate (task_controller (nClks prog), t with clock := t.clock + ck) =
      (SOME (Exception «panic» (ValWord 0w)), t') ∧
      code_installed t'.code prog ∧
      t'.ffi.ffi_state = next_ffi t.ffi.ffi_state ∧
      t'.ffi.oracle = t.ffi.oracle ∧
      t'.code = t.code ∧
      t'.be = t.be ∧ t'.base_addr = t.base_addr ∧
      t'.eshapes = t.eshapes ∧
      t'.locals = FEMPTY ∧
      input_io_events_rel i t t'

Proof
  rw [] >>
  fs [task_controller_def] >>
  fs [panLangTheory.nested_seq_def] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  qexists_tac ‘2’ >>
  pairarg_tac >> rgs [] >>
  pop_assum mp_tac >>
  fs [wait_input_time_limit_def] >>
  rewrite_tac [Once evaluate_def] >>
  ‘∃w. eval t wait = SOME (ValWord w) ∧ w ≠ 0w’ by (
    cases_on ‘s.waitTime’
    >- (
      rgs [state_rel_def, equivs_def, active_low_def] >>
      match_mp_tac step_delay_eval_wait_not_zero >>
      rgs [state_rel_def, equivs_def, time_vars_def, active_low_def]) >>
    ‘x ≠ 0’ by rgs [step_cases] >>
    match_mp_tac eval_wait_not_zero' >>
    rgs [input_rel_def, next_ffi_def] >>
    conj_tac
    >- rgs [state_rel_def, equivs_def, active_low_def, time_vars_def] >>
    qexists_tac ‘FST (t.ffi.ffi_state 1)’ >>
    rgs [] >>
    gvs [wakeup_shape_def, input_stime_rel_def] >>
    qexists_tac ‘wt'’ >>
    qexists_tac ‘ist’ >>
    rgs [input_rel_def, next_ffi_def] >>
    rgs [state_rel_def] >>
    pairarg_tac >> rgs [] >> rgs [] >>
    ‘FST (t.ffi.ffi_state 1) = FST (t.ffi.ffi_state 0)’ by (
      rgs [input_time_rel_def] >>
      last_x_assum (qspec_then ‘0’ mp_tac) >>
      rgs [input_time_eq_def, has_input_def]) >>
    gvs [step_cases]) >>
  rgs [eval_upd_clock_eq] >>
  rgs [dec_clock_def] >>
  (* evaluating the function *)
  pairarg_tac >> fs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once check_input_time_def] >>
  fs [panLangTheory.nested_seq_def] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  drule state_rel_imp_mem_config >>
  rewrite_tac [Once mem_config_def] >>
  strip_tac >>
  fs [] >>
  ‘∃bytes.
     read_bytearray t.base_addr (w2n (ffiBufferSize:'a word))
                    (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes’ by (
    match_mp_tac read_bytearray_some_bytes_for_ffi >>
    rgs []) >>
  drule evaluate_ext_call >>
  disch_then (qspecl_then [‘MAP explode (out_signals prog)’, ‘bytes’] mp_tac) >>
  impl_tac
  >- (
    rgs [state_rel_def] >>
    pairarg_tac >> rgs []) >>
  strip_tac >> rgs [] >>
  rveq >> rgs [] >>
  drule state_rel_imp_ffi_vars >>
  strip_tac >>
  pop_assum mp_tac >>
  rewrite_tac [Once ffi_vars_def] >>
  strip_tac >>
  drule state_rel_imp_systime_defined >>
  strip_tac >>
  (* reading systime *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
  ‘nt.memory nt.base_addr = Word (n2w (FST(t.ffi.ffi_state 1)))’ by (
    fs [Abbr ‘nt’] >>
    qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
    rgs [mem_read_ffi_results_def] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
    last_x_assum
    (qspecl_then
     [‘t with clock := t.clock + 1’,
      ‘ft’] mp_tac) >>
    impl_tac
    >- rgs [Abbr ‘ft’, nexts_ffi_def, GSYM ETA_AX] >>
    strip_tac >>
    rgs [Abbr ‘ft’, nexts_ffi_def]) >>
  drule evaluate_assign_load >>
  rgs [] >>
  disch_then (qspecl_then
              [‘t.base_addr’, ‘tm’,
               ‘n2w (FST (t.ffi.ffi_state 1))’] mp_tac) >>
  impl_tac
  >- (
    rgs [Abbr ‘nt’] >>
    fs [state_rel_def]) >>
  strip_tac >> fs [] >>
  (* reading input to the variable event *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «event» _, nnt)’ >>
  ‘nnt.memory (t.base_addr +  bytes_in_word) =
   Word (n2w (SND(t.ffi.ffi_state 1)))’ by (
    fs [Abbr ‘nnt’, Abbr ‘nt’] >>
    qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
    rgs [mem_read_ffi_results_def] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
    last_x_assum (qspecl_then [‘t with clock := t.clock + 1’, ‘ft’] mp_tac) >>
    impl_tac
    >- rgs [Abbr ‘ft’, nexts_ffi_def, GSYM ETA_AX] >>
    strip_tac >>
    rgs [Abbr ‘ft’, nexts_ffi_def, GSYM ETA_AX]) >>
  rgs [] >>
  drule evaluate_assign_load_next_address >>
  rgs [] >>
  disch_then (qspecl_then
              [‘t.base_addr’,
               ‘n2w (SND (nexts_ffi 0 t.ffi.ffi_state 1))’] mp_tac) >>
  impl_tac
  >- (
    rgs [Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
    rgs [state_rel_def, time_vars_def, FLOOKUP_UPDATE,
        nexts_ffi_def, mem_config_def]) >>
  strip_tac >>
  rveq >> rgs [] >>
  (* isInput *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘evaluate (Assign «isInput» _, nnnt)’ >>
  ‘nnnt.memory (t.base_addr +  bytes_in_word) =
   Word (n2w (SND(t.ffi.ffi_state 1)))’ by fs [Abbr ‘nnnt’] >>
  rgs [] >>
  ‘nnnt.memory (t.base_addr +  bytes_in_word) ≠ Word 0w’ by (
    rgs [input_rel_def, nexts_ffi_def, next_ffi_def] >>
    rgs [step_cases] >>
    drule pick_term_dest_eq >>
    strip_tac >>
    pop_assum mp_tac >>
    disch_then (qspec_then ‘SND (t.ffi.ffi_state 1) − 1’ mp_tac) >>
    impl_tac >- fs [] >>
    strip_tac >>
    ‘SND (t.ffi.ffi_state 1) − 1 + 1 = SND (t.ffi.ffi_state 1)’ by (
      match_mp_tac SUB_ADD >>
      cases_on ‘SND (t.ffi.ffi_state 1)’
      >- metis_tac [] >>
      metis_tac [one_leq_suc]) >>
    ‘SND (t.ffi.ffi_state 1) MOD dimword (:α) =
     SND (t.ffi.ffi_state 1)’ suffices_by metis_tac [] >>
    match_mp_tac LESS_MOD >>
    match_mp_tac lt_less_one >>
    metis_tac []) >>
  fs [] >>
  drule evaluate_assign_compare_next_address_uneq >>
  rgs [] >>
  disch_then (qspecl_then [‘t.base_addr’,
                           ‘n2w (SND (t.ffi.ffi_state 1))’] mp_tac) >>
  impl_tac
  >- (
    rgs [Abbr ‘nnnt’, Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
    rgs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
    rgs [nexts_ffi_def, mem_config_def]) >>
  strip_tac >>
  rgs [] >> rveq >> rgs [] >>
  (* If statement *)
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> fs [] >>
  drule evaluate_if_compare_sys_time >>
  disch_then (qspec_then ‘FST (t.ffi.ffi_state 1)’ mp_tac) >>
  impl_tac
  >- (
    unabbrev_all_tac >>
    rgs [FLOOKUP_UPDATE, nexts_ffi_def] >>
    rgs [step_cases, ADD1, state_rel_def, input_time_rel_def] >>
    pairarg_tac >> rgs [] >>
    last_x_assum (qspec_then ‘0’ mp_tac) >>
    rgs [input_time_eq_def, has_input_def, input_rel_def, next_ffi_def] >>
    strip_tac >>
    drule LESS_MOD >>
    strip_tac >> rgs []) >>
  strip_tac >> rveq >> rgs [] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  strip_tac >> fs [] >>
  rveq >> rgs [] >>
  strip_tac >>
  (* loop should break now *)
  fs [step_cases] >>
  rgs [input_rel_def] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  fs [wait_input_time_limit_def] >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  ‘FLOOKUP (nnnt with locals := nnnt.locals |+ («isInput» ,ValWord 0w)).locals
   «isInput» = SOME (ValWord 0w)’ by fs [FLOOKUP_UPDATE] >>
  drule step_input_eval_wait_zero >>
  impl_tac
  >- (
    unabbrev_all_tac >> rgs [] >>
    fs [FLOOKUP_UPDATE] >>
    rgs [state_rel_def, time_vars_def]) >>
  rgs [eval_upd_clock_eq] >>
  strip_tac >>
  strip_tac >>
  unabbrev_all_tac >>
  rveq >> rgs [] >>
  (* the new If statement *)
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, nnt)’ >>
  rewrite_tac [Once evaluate_def] >>
  fs [] >>
  pairarg_tac >> rgs [] >>
  pop_assum mp_tac >>
  rewrite_tac [Once evaluate_def] >>
  unabbrev_all_tac >>
  gvs [eval_def, FLOOKUP_UPDATE, asmTheory.word_cmp_def] >>
  rewrite_tac [Once evaluate_def] >>
  gvs [] >>
  strip_tac >> gvs [] >>
  (* until here *)
  qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, nnt)’ >>
  ‘FLOOKUP nnt.locals «loc» = FLOOKUP t.locals «loc»’ by
    fs [Abbr ‘nnt’, FLOOKUP_UPDATE] >>
  ‘nnt.code = t.code’ by
    fs [Abbr ‘nnt’, state_component_equality] >>
  ‘FST (t.ffi.ffi_state 1) = FST (t.ffi.ffi_state 0)’ by (
    rgs [state_rel_def] >>
    pairarg_tac >>
    rgs [input_time_rel_def, input_time_eq_def] >>
    last_x_assum (qspec_then ‘0’ mp_tac) >>
    impl_tac
    >- rgs [has_input_def, next_ffi_def] >>
    rgs []) >>
  ‘FLOOKUP nnt.locals «clks» = FLOOKUP t.locals «clks»’ by
    fs [Abbr ‘nnt’, FLOOKUP_UPDATE] >>
  (* calling the function *)
  (* location will come from equivs: state_rel *)
  imp_res_tac state_rel_imp_equivs >>
  fs [equivs_def] >>
  qmatch_asmsub_abbrev_tac
  ‘FLOOKUP _ «loc» = SOME (ValLabel loc)’ >>
  ‘FLOOKUP t.code loc =
   SOME
   ([(«clks» ,genShape (LENGTH (clksOf prog))); («event» ,One)],
    compTerms (clksOf prog) «clks» «event» tms)’ by (
    fs [code_installed_def] >>
    drule ALOOKUP_MEM >>
    strip_tac >>
    last_x_assum drule >>
    strip_tac >>
    fs [Abbr ‘loc’]) >>
  (* evaluation *)
  fs [Once evaluate_def] >>
  pairarg_tac >>
  fs [] >>
  fs [Once evaluate_def, eval_upd_clock_eq] >>
  rgs [Once eval_def, eval_upd_clock_eq, FLOOKUP_UPDATE] >>
  ‘FLOOKUP nnt.locals «sysTime» = SOME (ValWord (n2w (FST (t.ffi.ffi_state 0))))’ by
    rgs [Abbr ‘nnt’, FLOOKUP_UPDATE] >>
  drule eval_normalisedClks >>
  rgs [Abbr ‘nnt’,  FLOOKUP_UPDATE] >>
  qpat_x_assum ‘state_rel (clksOf prog) (out_signals prog) s t’ assume_tac >>
  drule state_rel_intro >>
  strip_tac >> rgs [] >>
  pairarg_tac >> rgs [] >>
  rgs [clocks_rel_def] >>
  disch_then (qspec_then ‘ns’ mp_tac) >>
  impl_tac
  >- (
    conj_tac
    >- rgs [EVERY_MEM, time_seq_def] >>
    fs [EVERY_MEM] >>
    rw [] >>
    rgs [clkvals_rel_def] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    fs [MEM_EL] >>
    first_x_assum (qspec_then ‘n'’ mp_tac) >>
    fs [] >>
    strip_tac >>
    ‘(EL n' (ZIP (clksOf prog,ns))) =
     (EL n' (clksOf prog),EL n' ns)’ by (
      match_mp_tac EL_ZIP >>
      rgs []) >>
    fs []) >>
  strip_tac >>
  fs [] >>
  fs [OPT_MMAP_def] >>
  fs [Once eval_def] >>
  qmatch_asmsub_abbrev_tac ‘(eval nnt)’ >>
  ‘(λa. eval nnt a) =
   eval nnt’ by metis_tac [ETA_AX] >>
  fs [] >>
  fs [timeLangTheory.nClks_def] >>
  ‘LENGTH (clksOf prog) = LENGTH ns’ by rgs [] >>
  rgs [] >>
  (* event eval *)
  rgs [Abbr ‘nnt’, eval_def, FLOOKUP_UPDATE, nexts_ffi_def] >>
  rgs [lookup_code_def] >>
  fs [timeLangTheory.nClks_def] >>
  ‘LENGTH (clksOf prog) = LENGTH ns’ by rgs [] >>
  drule (INST_TYPE
         [``:'a``|->``:'mlstring``,
          ``:'b``|->``:'a``] genshape_eq_shape_of) >>
  disch_then (qspec_then ‘tm’ assume_tac) >>
  rfs [] >>
  fs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  fs [shape_of_def] >>
  fs [dec_clock_def] >>
  pop_assum kall_tac >>
  qmatch_asmsub_abbrev_tac ‘(«clks» ,Struct nclks)’ >>
  qmatch_asmsub_abbrev_tac ‘evaluate (_, nnt)’ >>
  rgs [next_ffi_def] >>
  drule  (INST_TYPE [``:'a``|->``:'a``,
                     ``:'b``|->``:time_input``] pick_term_thm) >>
  fs [] >>
  disch_then (qspecl_then [‘nnt’, ‘clksOf prog’,
                           ‘nclks’] mp_tac) >>
  impl_tac
  >- (
    rgs [Abbr ‘nnt’] >>
    res_tac >> rgs [] >> rveq >>
    rgs [well_formed_terms_def] >>
    conj_tac
    >- (
      match_mp_tac mem_to_flookup >>
      fs []) >>
    conj_tac
    >- rgs [resetOutput_def, defined_clocks_def] >>
    conj_tac
    >- (
      fs [resetOutput_def, Abbr ‘nclks’] >>
      rgs [clkvals_rel_def, equiv_val_def] >>
      fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >>
      first_x_assum (qspec_then ‘n’ mp_tac) >>
      fs [] >>
      strip_tac >>
      qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,_))’ >>
      ‘EL n (ZIP (xs,ns)) = (EL n xs, EL n ns)’ by (
      match_mp_tac EL_ZIP >>
      unabbrev_all_tac >>
      fs []) >>
      fs [Abbr ‘xs’] >>
      ‘EL n (REPLICATE (LENGTH ns) (FST (t.ffi.ffi_state 1))) = FST (t.ffi.ffi_state 1)’ by (
      match_mp_tac EL_REPLICATE >>
      fs []) >>
      fs [] >>
      ‘EL n (ZIP (clksOf prog,ns)) = (EL n (clksOf prog), EL n ns)’ by (
        match_mp_tac EL_ZIP >>
        unabbrev_all_tac >>
        fs []) >>
      fs []) >>
    conj_tac
    >- (
      rgs [Abbr ‘nclks’, defined_clocks_def, maxClksSize_def] >>
      fs [MAP_MAP_o] >>
      fs [SUM_MAP_FOLDL] >>
      ‘LENGTH (REPLICATE (LENGTH ns) (FST (t.ffi.ffi_state 1))) = LENGTH ns’ by fs [] >>
      drule foldl_word_size_of >>
      disch_then (qspec_then ‘0’ mp_tac) >>
      fs []) >>
    rgs [resetOutput_def] >>
    rgs [out_signals_ffi_def, well_behaved_ffi_def] >>
    rgs [EVERY_MEM] >>
    gen_tac >>
    strip_tac >>
    rgs [] >>
    conj_tac
    >- rgs [mlintTheory.num_to_str_thm] >>
    conj_tac
    >- rgs [ffiBufferSize_def, bytes_in_word_def,
           good_dimindex_def] >>
    rgs [mem_call_ffi_def, ffi_call_ffi_def] >>
    qmatch_goalsub_abbrev_tac ‘mem_load_byte mm _ _’ >>
    ‘∃bytes.
       read_bytearray t.base_addr (w2n (ffiBufferSize:'a word))
              (mem_load_byte mm t.memaddrs t.be) = SOME bytes’ by (
      match_mp_tac read_bytearray_some_bytes_for_ffi >>
      rgs [state_rel_def, mem_config_def]) >>
    qexists_tac ‘bytes'’ >> rgs [] >>
    rgs [next_ffi_def, build_ffi_def] >>
    rgs [ffiTheory.ffi_state_component_equality] >>
    ‘MEM tms (MAP SND prog)’ by (
      drule ALOOKUP_MEM >>
      rgs [MEM_MAP] >>
      strip_tac >>
      qexists_tac ‘(s.location,tms)’ >>
      rgs []) >>
    ‘MEM (explode (toString out)) (MAP explode (out_signals prog))’ by (
      rgs [timeLangTheory.out_signals_def] >>
      rgs [MEM_MAP] >>
      qexists_tac ‘out’ >> rgs [] >>
      match_mp_tac terms_out_signals_prog >>
      qexists_tac ‘tms’ >>
      rgs [MEM_MAP] >>
      metis_tac []) >>
    cases_on ‘explode (num_to_str out) = "get_time_input"’ >>
    rgs []) >>
  impl_tac
  >- (
    fs [Abbr ‘nnt’] >>
    conj_tac
    >- (
      drule pick_term_dest_eq >>
      strip_tac >>
      pop_assum mp_tac >>
      disch_then (qspec_then ‘SND (t.ffi.ffi_state 1) − 1’ mp_tac) >>
      impl_tac >- fs [] >>
      strip_tac >>
      ‘SND (t.ffi.ffi_state 1) − 1 + 1 < dimword (:α)’ by (
        match_mp_tac lt_less_one >>
        metis_tac []) >>
      ‘1 ≤ SND (t.ffi.ffi_state 1)’ by (
        cases_on ‘SND (t.ffi.ffi_state 1)’
        >- metis_tac [] >>
        metis_tac [one_leq_suc]) >>
      drule SUB_ADD >>
      strip_tac >>
      metis_tac []) >>
    (* from pick_term theorem  *)
    match_mp_tac mem_to_flookup >>
    fs []) >>
  strip_tac >> gvs [] >>
  unabbrev_all_tac >>
  gvs [empty_locals_def, ffi_call_ffi_def, next_ffi_def] >>
  rgs [input_io_events_rel_def] >>
  conj_asm1_tac
  >- (
    qexists_tac ‘bytes’ >>
    rgs [mk_ti_event_def, time_input_def] >>
    drule read_bytearray_LENGTH >>
    strip_tac >>
    rgs [ffiBufferSize_def, good_dimindex_def,
        bytes_in_word_def, dimword_def]) >>
  conj_asm1_tac
  >- (
    rgs [from_io_events_def, DROP_LENGTH_APPEND, io_events_dest_def,
        mk_ti_event_def, io_event_dest_def, time_input_def] >>
    qmatch_goalsub_abbrev_tac ‘ZIP (_, nbytes)’ >>
    ‘LENGTH bytes' = LENGTH nbytes’ by (
      fs [Abbr ‘nbytes’, length_get_bytes] >>
      rgs [good_dimindex_def]) >>
    drule MAP_ZIP >>
    rgs [] >>
    strip_tac >>
    ‘words_of_bytes t.be nbytes =
     [n2w(FST (t.ffi.ffi_state 1)); (n2w(SND (t.ffi.ffi_state 1))):'a word]’ by (
      fs [Abbr ‘nbytes’] >>
      match_mp_tac words_of_bytes_get_bytes >>
      rgs []) >>
    rgs [input_eq_ffi_seq_def] >>
    cases_on ‘t.ffi.ffi_state 1’ >> rgs [] >>
    rgs [input_rel_def, step_cases, next_ffi_def] >>
    drule pick_term_dest_eq >>
    simp []) >>
  rgs [from_io_events_def, DROP_LENGTH_APPEND, input_eq_ffi_seq_def] >>
  rgs [DROP_LENGTH_APPEND, decode_io_events_def, io_events_dest_def,
      mk_ti_event_def, decode_io_event_def]  >>
  cases_on ‘t.ffi.ffi_state 1’ >> rgs [] >>
  rgs [to_input_def]
QED


Theorem steps_sts_length_eq_lbls:
  ∀lbls prog m n st sts.
    steps prog lbls m n st sts ⇒
    LENGTH sts = LENGTH lbls
Proof
  Induct >>
  rw [] >>
  cases_on ‘sts’ >>
  gs [steps_def] >>
  res_tac >> gs []
QED


Theorem steps_thm:
  ∀labels prog n ist st sts (t:('a,time_input) panSem$state).
    steps prog labels (dimword (:α) - 1) n st sts ∧
    assumptions prog n st t ⇒
     evaluations prog labels sts ist st t
Proof
  Induct
  >- (
    rpt gen_tac >>
    strip_tac >>
    cases_on ‘sts’ >>
    fs [evaluations_def, steps_def]) >>
  rpt gen_tac >>
  strip_tac >>
  ‘LENGTH sts = LENGTH (h::labels')’ by
    metis_tac [steps_sts_length_eq_lbls] >>
  cases_on ‘sts’ >>
  fs [] >>
  ‘n = FST (t.ffi.ffi_state 0)’ by
    gs [assumptions_def] >>
  rveq >> gs [] >>
  cases_on ‘h’ >> gs []
  >- ((* delay step *)
    gs [steps_def] >>
    gs [assumptions_def, evaluations_def, event_inv_def] >>
    rveq >> gs [] >>
    rw [] >>
    drule step_delay >>
    gs [] >>
    disch_then (qspecl_then [‘cycles’, ‘t’, ‘0’, ‘ist’] mp_tac) >>
    impl_tac
    >- (gs [] >> gs[state_rel_def])>>
    strip_tac >>
    qexists_tac ‘ck+1’ >>
    gs [always_def] >>
    once_rewrite_tac [panSemTheory.evaluate_def] >>
    gs [panSemTheory.eval_def] >>
    gs [panSemTheory.dec_clock_def] >>
    qexists_tac ‘t'' with clock := t''.clock + 1’ >>
    conj_tac
    >- rw [] >>
    gs [] >>
    conj_asm1_tac
    >- gs [state_rel_def] >>
    gs [] >>
    conj_asm1_tac
    >- (
      rewrite_tac [wait_time_locals1_def] >>
      gs [step_cases, mkState_def]
      >- (
        gs [wakeup_shape_def] >>
        qexists_tac ‘wt'’ >>
        gs []) >>
      gs [wakeup_shape_def] >>
      qexists_tac ‘wt'’ >>
      gs [] >>
      strip_tac >>
      gs [wakeup_rel_def, nexts_ffi_def] >>
      last_x_assum (qspec_then ‘cycles’ mp_tac) >>
      gs []) >>
    conj_asm1_tac
    >- (
      gs [delay_io_events_rel_def] >>
      metis_tac []) >>
    conj_asm1_tac
    >- (
      gs [obs_ios_are_label_delay_def] >>
      metis_tac []) >>
    conj_asm1_tac
    >- gs [task_ret_defined_def] >>
    last_x_assum match_mp_tac >>
    gs [nexts_ffi_def, delay_rep_def])
  >- (
    cases_on ‘i’ >>
    gs []
    >- (
      (* input step *)
      gs [steps_def] >>
      gs [assumptions_def, evaluations_def, event_inv_def] >>
      rveq >> gs [] >>
      rw [] >>
      drule step_input >>
      gs [] >>
      disch_then (qspecl_then [‘t’,‘FST (t.ffi.ffi_state 0)’] mp_tac) >>
      impl_tac
      >- (
      gs [timeSemTheory.step_cases] >>
      gs [well_formed_code_def]) >>
      strip_tac >>
      ‘FST (next_ffi t.ffi.ffi_state 0) = FST (t.ffi.ffi_state 0)’ by (
      gs [state_rel_def] >>
      pairarg_tac >> gs [] >>
      gs [input_time_rel_def] >>
      pairarg_tac >> gs [] >>
      gs [input_time_eq_def, has_input_def] >>
      last_x_assum (qspec_then ‘0’ mp_tac) >>
      impl_tac
      >- (
        gs [] >>
        gs [input_rel_def, next_ffi_def]) >>
      gs [next_ffi_def]) >>
    qexists_tac ‘ck+1’ >>
    gs [always_def] >>
    rewrite_tac [Once panSemTheory.evaluate_def] >>
    gs [panSemTheory.eval_def] >>
    gs [panSemTheory.dec_clock_def] >>
    qexists_tac ‘t''’ >>
    fs [] >>
    conj_tac
    >- (
      rw [] >>
      drule evaluate_add_clock_eq >>
      gs []) >>
    cases_on ‘h'.waitTime’ >>
    gs [wait_time_locals1_def]
    >- (
      qexists_tac ‘0’ >>
      gs [good_dimindex_def, dimword_def]) >>
    qexists_tac ‘x’ >>
    gs [step_cases] >>
    drule pick_term_dest_eq >>
    gs []) >>
  (* output step *)
  gs [steps_def] >>
  gs [assumptions_def, event_inv_def, evaluations_def, event_inv_def] >>
  rveq >> gs [] >>
  rw [] >>
  drule step_output >>
  gs [] >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  impl_tac
  >- (
    gs [timeSemTheory.step_cases] >>
    gs [well_formed_code_def]) >>
  strip_tac >>
  qexists_tac ‘ck+1’ >>
  gs [always_def] >>
  rewrite_tac [Once panSemTheory.evaluate_def] >>
  gs [panSemTheory.eval_def] >>
  gs [panSemTheory.dec_clock_def] >>
  qexists_tac ‘t''’ >>
  fs [] >>
  conj_tac
  >- (
    rw [] >>
    drule evaluate_add_clock_eq >>
    gs []) >>
  cases_on ‘h'.waitTime’ >>
  gs [wait_time_locals1_def]
  >- (
    qexists_tac ‘0’ >>
    gs [good_dimindex_def, dimword_def]) >>
  qexists_tac ‘x’ >>
  gs [] >>
  gs [step_cases] >>
    drule pick_term_dest_eq >>
    gs []) >>
  cases_on ‘p’ >>
  gs []
  >- (
  gs [steps_def] >>
  gs [assumptions_def, evaluations_def, event_inv_def] >>
  rveq >> gs [] >>
  rw [] >>
  drule step_panic_timeout >>
  gs [] >>
  disch_then (qspec_then ‘t’ mp_tac) >>
  impl_tac
  >- (
    gs [timeSemTheory.step_cases] >>
    gs [well_formed_code_def,state_rel_def]) >>
  strip_tac >>
  qexists_tac ‘ck+1’ >>
  gs [always_def] >>
  rewrite_tac [Once panSemTheory.evaluate_def] >>
  gs [panSemTheory.eval_def] >>
  gs [panSemTheory.dec_clock_def] >>
  qexists_tac ‘t''’ >>
  fs [] >>
  rw [] >> gvs [] >>
  drule evaluate_add_clock_eq >>
  gs []) >>
  (* input step *)
  gs [steps_def] >>
  gs [assumptions_def, evaluations_def, event_inv_def] >>
  rveq >> gs [] >>
  rw [] >>
  drule step_panic_input >>
  gs [] >>
  disch_then (qspecl_then [‘t’,‘FST (t.ffi.ffi_state 0)’] mp_tac) >>
  impl_tac
  >- (
  gs [timeSemTheory.step_cases] >>
  gs [well_formed_code_def,state_rel_def]) >>
  strip_tac  >>
  qexists_tac ‘ck+1’ >>
  gs [always_def] >>
  rewrite_tac [Once panSemTheory.evaluate_def] >>
  gs [panSemTheory.eval_def] >>
    gs [panSemTheory.dec_clock_def] >>
  qexists_tac ‘t''’ >>
  fs [] >>
  rw [] >> gvs [] >>
  drule evaluate_add_clock_eq >>
  gs []
QED


Theorem decode_ios_length_eq_sum:
  ∀labels ns ios be.
    decode_ios (:α) be labels ns ios ∧
    LENGTH labels = LENGTH ns  ⇒
    SUM ns = LENGTH ios - 1
Proof
  Induct >>
  rw [] >>
  gs [decode_ios_def] >>
  cases_on ‘ns’ >> gs [decode_ios_def]
QED

Theorem drop_length_eq_last:
  ∀xs.
    xs ≠ [] ⇒
    DROP (LENGTH xs − 1) xs = [LAST xs]
Proof
  Induct >>
  rw [] >>
  cases_on ‘xs = []’ >> gs [LAST_CONS_cond] >>
  ‘DROP (LENGTH xs) (h::xs) = DROP (LENGTH xs - 1) xs’ by (
    match_mp_tac DROP_cons >>
    gs [] >>
    cases_on ‘xs’ >> gs []) >>
  gs []
QED

Definition sum_delays_def:
  sum_delays (:α) lbls (ffi:time_input) ⇔
    SUM (MAP (λlbl.
               case lbl of
               | LDelay d => d
               | _ => 0) lbls) + FST (ffi 0) = dimword (:α) − 2 ∧
    (∀n.
       FST (ffi n) = dimword (:α) − 2 ⇒
       ffi (n+1) = (dimword (:α) − 1, 0) ∧
       SND (ffi n) = 0 ∧
       mem_read_ffi_results (:α) ffi (n+1))
End

Definition no_panic_def:
  no_panic lbls ⇔
  ∀lbl.
    MEM lbl lbls ⇒
    lbl ≠ LPanic (PanicTimeout) ∧
    (∀is. lbl ≠ LPanic is)
End

Theorem steps_io_event_no_panic_thm:
  ∀labels prog n st sts (t:('a,time_input) panSem$state) ist.
    steps prog labels (dimword (:α) - 1) n st sts ∧
    no_panic labels ∧
    assumptions prog n st t ∧
    ffi_rels prog labels st t ist ∧
    sum_delays (:α) labels t.ffi.ffi_state ⇒
    ∃ck t' ns ios.
      evaluate (time_to_pan$always (nClks prog), t with clock := t.clock + ck) =
      (SOME (Return (ValWord 0w)),t') ∧
      t'.ffi.io_events = t.ffi.io_events ++ ios ∧
      LENGTH labels = LENGTH ns ∧
      SUM ns + 1 = LENGTH ios ∧
      t'.be = t.be ∧ t'.base_addr = t.base_addr ∧
      decode_ios (:α) t'.be labels ns
                 (LAST t.ffi.io_events::TAKE (SUM ns) ios)
Proof
  rw [] >>
  gs [no_panic_def] >>
  drule_all steps_thm >>
  disch_then (qspec_then ‘ist’ mp_tac) >>
  strip_tac >>
  rpt (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [‘ist’, ‘t’, ‘sts’, ‘st’, ‘n’, ‘prog’, ‘labels'’] >>
  Induct
  >- (
    rw [] >>
    cases_on ‘sts’ >>
    fs [evaluations_def, steps_def] >>
    gs [sum_delays_def] >>
    qexists_tac ‘2’ >>
    gs [always_def] >>
    once_rewrite_tac [panSemTheory.evaluate_def] >>
    gs [panSemTheory.eval_def] >>
    gs [panSemTheory.dec_clock_def] >>
    pairarg_tac >> gs [] >>
    pop_assum mp_tac >>
    fs [task_controller_def] >>
    fs [panLangTheory.nested_seq_def] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> gs [] >>
    pop_assum mp_tac >>
    fs [wait_input_time_limit_def] >>
    rewrite_tac [Once evaluate_def] >>
    ‘FLOOKUP t.locals «isInput» = SOME (ValWord 1w)’ by
      gs [assumptions_def, event_inv_def] >>
    ‘∃w. eval t wait = SOME (ValWord w)’ by (
      cases_on ‘st.waitTime’
      >- (
        ‘FLOOKUP t.locals «waitSet» = SOME (ValWord 1w)’ by
           gs [assumptions_def, state_rel_def, equivs_def, active_low_def] >>
        drule step_delay_eval_wait_not_zero >>
        impl_tac
        >- gs [assumptions_def, state_rel_def, mkState_def,
               equivs_def, time_vars_def, active_low_def] >>
        gs [] >> metis_tac []) >>
      gs [] >>
      ‘FLOOKUP t.locals «waitSet» = SOME (ValWord 0w)’ by
        gs [assumptions_def, state_rel_def, equivs_def, active_low_def] >>
      gvs [wait_def, eval_def, OPT_MMAP_def, assumptions_def, state_rel_def] >>
      pairarg_tac >> gs [] >>
      gs [ffi_rels_def] >>
      gs [wait_time_locals1_def] >>
      gs [asmTheory.word_cmp_def] >>
      cases_on ‘(ist + wt) MOD dimword (:α) ≠ dimword (:α) − 2’ >>
      gvs [wordLangTheory.word_op_def]) >>
    reverse (cases_on ‘w = 0w’) >> gvs []
    >- (
      gs [eval_upd_clock_eq] >>
      pairarg_tac >> fs [] >>
      pop_assum mp_tac >>
      fs [dec_clock_def] >>
      rewrite_tac [Once check_input_time_def] >>
      fs [panLangTheory.nested_seq_def] >>
      rewrite_tac [Once evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      gs [assumptions_def] >>
      drule state_rel_imp_mem_config >>
      rewrite_tac [Once mem_config_def] >>
      strip_tac >>
      fs [] >>
      ‘∃bytes.
         read_bytearray t.base_addr (w2n (ffiBufferSize:'a word))
                        (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes’ by (
        match_mp_tac read_bytearray_some_bytes_for_ffi >>
        gs [state_rel_def]) >>
      drule evaluate_ext_call >>
      disch_then (qspecl_then [‘MAP explode (out_signals prog)’,‘bytes’] mp_tac) >>
      impl_tac
      >- (
      gs [state_rel_def] >>
      pairarg_tac >> gs []) >>
      strip_tac >> gs [] >> rveq >> gs [] >>
      pop_assum kall_tac >>
      drule state_rel_imp_ffi_vars >>
      strip_tac >>
      pop_assum mp_tac >>
      rewrite_tac [Once ffi_vars_def] >>
      strip_tac >>
      drule state_rel_imp_systime_defined >>
      strip_tac >>
      (* reading systime *)
      rewrite_tac [Once evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
      ‘nt.memory nt.base_addr = Word (n2w (FST(t.ffi.ffi_state 1)))’ by (
        fs [Abbr ‘nt’] >>
        last_x_assum (qspec_then ‘0’ mp_tac) >>
        impl_tac >- gs [] >>
        strip_tac >>
        gs [mem_read_ffi_results_def] >>
        qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
        last_x_assum
        (qspecl_then
         [‘t with clock := t.clock’,
          ‘ft’] mp_tac) >>
        impl_tac
        >- gs [Abbr ‘ft’,  nexts_ffi_def, GSYM ETA_AX] >>
        strip_tac >>
        gs [Abbr ‘ft’, nexts_ffi_def, GSYM ETA_AX]) >>
      drule evaluate_assign_load >>
      gs [] >>
      disch_then (qspecl_then
                  [‘t.base_addr’, ‘tm’,
                   ‘n2w (FST (t.ffi.ffi_state 1))’] mp_tac) >>
      impl_tac
      >- (
      gs [Abbr ‘nt’] >>
      fs [state_rel_def]) >>
      strip_tac >> fs [] >> rveq >> gs [] >>
      pop_assum kall_tac >>
      (* reading input to the variable event *)
      rewrite_tac [Once evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (Assign «event» _, nnt)’ >>
      ‘nnt.memory (nnt.base_addr +  bytes_in_word) =
       Word (n2w (SND(t.ffi.ffi_state 1)))’ by (
        fs [Abbr ‘nnt’, Abbr ‘nt’] >>
        last_x_assum (qspec_then ‘0’ mp_tac) >>
        impl_tac >- gs [] >>
        strip_tac >>
        gs [mem_read_ffi_results_def] >>
        qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
        last_x_assum
        (qspecl_then
         [‘t with clock := t.clock’,
          ‘ft’] mp_tac) >>
        impl_tac
        >- gs [Abbr ‘ft’,  nexts_ffi_def, GSYM ETA_AX] >>
        strip_tac >>
        gs [Abbr ‘ft’,  nexts_ffi_def, GSYM ETA_AX]) >>
      gs [] >>
      drule evaluate_assign_load_next_address >>
      gs [] >>
      disch_then (qspecl_then
                  [‘nnt.base_addr’,
                   ‘n2w (SND (t.ffi.ffi_state 1))’] mp_tac) >>
      impl_tac
      >- (
      gs [Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
      gs [state_rel_def, time_vars_def, FLOOKUP_UPDATE]) >>
      strip_tac >>
      gs [] >> rveq >> gs [] >>
      (* isInput *)
      rewrite_tac [Once evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (Assign «isInput» _, nnnt)’ >>
      ‘nnnt.memory (nnnt.base_addr +  bytes_in_word) =
       Word (n2w (SND(t.ffi.ffi_state 1)))’ by fs [Abbr ‘nnnt’] >>
      gs [] >>
      drule evaluate_assign_compare_next_address >>
      gs [] >>
      disch_then (qspecl_then [‘nnnt.base_addr’] mp_tac) >>
      impl_tac
      >- (
      gs [Abbr ‘nnnt’, Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
      gs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
      last_x_assum (qspec_then ‘0’ mp_tac) >>
      impl_tac >- gs [] >>
      gs []) >>
      strip_tac >>
      gs [] >> rveq >> gs [] >>
      (* If statement *)
      rewrite_tac [Once evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      drule evaluate_if_compare_sys_time1 >>
      disch_then (qspec_then ‘FST (t.ffi.ffi_state 1)’ mp_tac) >>
      impl_tac
      >- (
      unabbrev_all_tac >>
      gs [FLOOKUP_UPDATE, ADD1] >>
      last_x_assum (qspec_then ‘0’ mp_tac) >>
      impl_tac >- gs [] >>
      gs []) >>
      unabbrev_all_tac >> gs [] >>
      rpt strip_tac >> gs [empty_locals_def] >> rveq >>
      gs [ffi_call_ffi_def, state_component_equality] >>
      gs [decode_ios_def]) >>
    gs [eval_upd_clock_eq] >>
    strip_tac >> gvs [] >>
    ‘FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w (FST (t.ffi.ffi_state 0))))’ by (
      gvs [assumptions_def, state_rel_def] >>
      pairarg_tac >> gvs []) >>
    gvs [] >>
    qmatch_goalsub_abbrev_tac ‘evaluate (Seq _ q, _)’ >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    gs [eval_def, asmTheory.word_cmp_def] >>
    rewrite_tac [Once check_input_time_def] >>
    fs [panLangTheory.nested_seq_def] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    gs [assumptions_def] >>
    drule state_rel_imp_mem_config >>
    rewrite_tac [Once mem_config_def] >>
    strip_tac >>
    fs [] >>
    ‘∃bytes.
       read_bytearray t.base_addr (w2n (ffiBufferSize:'a word))
                      (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes’ by (
      match_mp_tac read_bytearray_some_bytes_for_ffi >>
      gs [state_rel_def]) >>
    drule evaluate_ext_call >>
    disch_then (qspecl_then [‘MAP explode (out_signals prog)’,‘bytes’] mp_tac) >>
    impl_tac
    >- (
    gs [state_rel_def] >>
    pairarg_tac >> gs []) >>
    strip_tac >> gs [] >> rveq >> gs [] >>
    pop_assum kall_tac >>
    drule state_rel_imp_ffi_vars >>
    strip_tac >>
    pop_assum mp_tac >>
    rewrite_tac [Once ffi_vars_def] >>
    strip_tac >>
    drule state_rel_imp_systime_defined >>
    strip_tac >>
    (* reading systime *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
    ‘nt.memory nt.base_addr = Word (n2w (FST(t.ffi.ffi_state 1)))’ by (
      fs [Abbr ‘nt’] >>
      last_x_assum (qspec_then ‘0’ mp_tac) >>
      impl_tac >- gs [] >>
      strip_tac >>
      gs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
      last_x_assum
      (qspecl_then
       [‘t with clock := t.clock + 1’,
        ‘ft’] mp_tac) >>
      impl_tac
      >- gs [Abbr ‘ft’,  nexts_ffi_def, GSYM ETA_AX] >>
      strip_tac >>
      gs [Abbr ‘ft’, nexts_ffi_def, GSYM ETA_AX]) >>
      drule evaluate_assign_load >>
    gs [] >>
    disch_then (qspecl_then
                [‘nt.base_addr’, ‘tm’,
                 ‘n2w (FST (t.ffi.ffi_state 1))’] mp_tac) >>
    impl_tac
    >- (
      gs [Abbr ‘nt’] >>
      fs [state_rel_def]) >>
    strip_tac >> fs [] >> rveq >> gs [] >>
    pop_assum kall_tac >>
    (* reading input to the variable event *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «event» _, nnt)’ >>
    ‘nnt.memory (nnt.base_addr +  bytes_in_word) =
       Word (n2w (SND(t.ffi.ffi_state 1)))’ by (
        fs [Abbr ‘nnt’, Abbr ‘nt’] >>
        last_x_assum (qspec_then ‘0’ mp_tac) >>
        impl_tac >- gs [] >>
        strip_tac >>
        gs [mem_read_ffi_results_def] >>
        qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, _) = (_, ft)’ >>
        last_x_assum
        (qspecl_then
         [‘t with clock := t.clock + 1’,
          ‘ft’] mp_tac) >>
        impl_tac
        >- gs [Abbr ‘ft’,  nexts_ffi_def, GSYM ETA_AX] >>
        strip_tac >>
        gs [Abbr ‘ft’,  nexts_ffi_def, GSYM ETA_AX]) >>
      gs [] >>
      drule evaluate_assign_load_next_address >>
      gs [] >>
      disch_then (qspecl_then
                  [‘nnt.base_addr’,
                   ‘n2w (SND (t.ffi.ffi_state 1))’] mp_tac) >>
      impl_tac
      >- (
      gs [Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
      gs [state_rel_def, time_vars_def, FLOOKUP_UPDATE]) >>
      strip_tac >>
      gs [] >> rveq >> gs [] >>
      (* isInput *)
      rewrite_tac [Once evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (Assign «isInput» _, nnnt)’ >>
      ‘nnnt.memory (nnnt.base_addr +  bytes_in_word) =
       Word (n2w (SND(t.ffi.ffi_state 1)))’ by fs [Abbr ‘nnnt’] >>
      gs [] >>
      drule evaluate_assign_compare_next_address >>
      gs [] >>
      disch_then (qspecl_then [‘nnnt.base_addr’] mp_tac) >>
      impl_tac
      >- (
      gs [Abbr ‘nnnt’, Abbr ‘nnt’,Abbr ‘nt’, active_low_def] >>
      gs [state_rel_def, time_vars_def, FLOOKUP_UPDATE] >>
      last_x_assum (qspec_then ‘0’ mp_tac) >>
      impl_tac >- gs [] >>
      gs []) >>
      strip_tac >>
      gs [] >> rveq >> gs [] >>
      (* If statement *)
      rewrite_tac [Once evaluate_def] >>
      fs [] >>
      pairarg_tac >> fs [] >>
      drule evaluate_if_compare_sys_time1 >>
      disch_then (qspec_then ‘FST (t.ffi.ffi_state 1)’ mp_tac) >>
      impl_tac
      >- (
      unabbrev_all_tac >>
      gs [FLOOKUP_UPDATE, ADD1] >>
      last_x_assum (qspec_then ‘0’ mp_tac) >>
      impl_tac >- gs [] >>
      gs []) >>
      unabbrev_all_tac >> gs [] >>
      rpt strip_tac >> gs [empty_locals_def] >> rveq >>
      gs [ffi_call_ffi_def, state_component_equality] >>
      gs [decode_ios_def]) >>
  rw [] >>
  ‘LENGTH sts = LENGTH (h::labels')’ by
    metis_tac [steps_sts_length_eq_lbls] >>
  cases_on ‘sts’ >>
  fs [] >>
  ‘n = FST (t.ffi.ffi_state 0)’ by
    gs [assumptions_def] >>
  rveq >> gs [] >>
  gs [evaluations_def, steps_def] >>
  cases_on ‘h’ >> gs [] >>
  TRY (
    cases_on ‘p’ >> gvs []
    >- (
      first_x_assum (qspec_then ‘LPanic PanicTimeout’ mp_tac) >>
      gvs []) >>
    first_x_assum (qspec_then ‘LPanic (PanicInput n)’ mp_tac) >>
    gvs [])
  >- (
    gs [ffi_rels_def, ffi_rel_def] >>
    first_x_assum drule >>
    gs [] >>
    strip_tac >>
    last_x_assum drule >>
    disch_then (qspecl_then [‘nt’, ‘ist’] mp_tac) >>
    impl_tac
    >- (
      gs [assumptions_def] >>
      gs [nexts_ffi_def, delay_rep_def] >>
      conj_tac
      >- (
        first_x_assum match_mp_tac >>
        metis_tac []) >>
      once_rewrite_tac [sum_delays_def] >>
      conj_tac >- gs [sum_delays_def] >>
      gs [sum_delays_def] >>
      gen_tac >>
      strip_tac >>
      first_x_assum (qspec_then ‘cycles + n'’ mp_tac) >>
      first_x_assum (qspec_then ‘cycles + n'’ mp_tac) >>
      gs [] >>
      strip_tac >>
      strip_tac >>
      gs [mem_read_ffi_results_def] >>
      rpt gen_tac >>
      strip_tac >>
      first_x_assum (qspec_then ‘i + cycles’ mp_tac) >>
      gs [nexts_ffi_def] >>
      disch_then
      (qspec_then ‘t'' with ffi :=
                   (t''.ffi with ffi_state :=
                    (λn''. t.ffi.ffi_state (cycles + (i + n''))))’ mp_tac) >>
      gs [] >>
      disch_then (qspec_then ‘t'''’ mp_tac) >>
      impl_tac
      >- (
        gs [] >>
        ‘t'' with
         ffi :=
         t''.ffi with
          ffi_state := (λn''. t.ffi.ffi_state (cycles + (i + n''))) =
         t''’ by
          gs [state_component_equality, ffiTheory.ffi_state_component_equality] >>
        gs []) >>
      gs []) >>
    strip_tac >>
    first_x_assum (qspec_then ‘ck'’ assume_tac) >>
    qexists_tac ‘ck + ck'’ >> gs [] >>
    gs [delay_io_events_rel_def] >>
    qexists_tac ‘cycles::ns’ >>
    rewrite_tac [decode_ios_def] >>
    gs [] >>
    TOP_CASE_TAC
    >- (
      gs [mk_ti_events_def, gen_ffi_states_def] >>
      gs [delay_rep_def] >>
      drule decode_ios_length_eq_sum >>
      gs []) >>
    conj_asm1_tac
    >-  gs [mk_ti_events_def, gen_ffi_states_def] >>
    (*
     gs [] >>
     cases_on ‘ios’ >>
     gvs [FRONT_APPEND]*)
    conj_asm1_tac
    >- gs [TAKE_SUM] >>
    qmatch_asmsub_abbrev_tac ‘decode_ios _ _ _ ns nios’ >>
    qmatch_goalsub_abbrev_tac ‘decode_ios _ _ _ ns nios'’ >>
    ‘nios = nios'’ by (
      gs [Abbr ‘nios’, Abbr ‘nios'’] >>
      gs [TAKE_SUM] >>
      qmatch_goalsub_abbrev_tac ‘TAKE _ (xs ++ _)’ >>
      ‘cycles = LENGTH xs’ by
        gs [Abbr ‘xs’, mk_ti_events_def, gen_ffi_states_def] >>
      gs [TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
      gs [DROP_APPEND] >>
      ‘LENGTH xs − 1 − LENGTH xs = 0’ by gs [] >>
      simp [] >>
      pop_assum kall_tac >>
      ‘DROP (LENGTH xs − 1) xs = [LAST xs]’ by (
        match_mp_tac drop_length_eq_last >>
        CCONTR_TAC >>
        gvs []) >>
      gs [] >>
      ‘cycles = LENGTH xs’ by gvs [] >>
      cases_on ‘xs’ >- gs [] >>
      simp [LAST_APPEND_CONS] >> gvs [] >>
      ‘LENGTH t'³' − SUC (LENGTH t'³') = 0’ by gs [] >>
      simp [] >>
      gs [DROP_LENGTH_NIL, TAKE_LENGTH_APPEND, LAST_CONS_cond] >>
      cases_on ‘t'''’ >> gvs []) >>
    qpat_x_assum ‘obs_ios_are_label_delay _ _ _’ mp_tac >>
    gs [obs_ios_are_label_delay_def] >>
    strip_tac >>
    pop_assum mp_tac >>
    impl_tac
    >- (
      CCONTR_TAC >>
      gs [DROP_LENGTH_APPEND, mk_ti_events_def, gen_ffi_states_def, decode_io_events_def] >>
      gs [ZIP_EQ_NIL]) >>
    strip_tac >>
    gs [] >>
    qmatch_goalsub_abbrev_tac ‘TAKE _ (TAKE _ (xs ++ _))’ >>
    ‘TAKE cycles (TAKE (cycles + SUM ns) (xs ++ ios)) =
     xs’ by (
      ‘cycles = LENGTH xs’ by
         gs [Abbr ‘xs’, mk_ti_events_def, gen_ffi_states_def] >>
      simp [] >>
      gs [TAKE_SUM, TAKE_LENGTH_APPEND]) >>
    gs [Abbr ‘xs’, DROP_LENGTH_APPEND]) >>
  cases_on ‘i’
  >- (
    gs [ffi_rels_def, ffi_rel_def, action_rel_def] >>
    first_x_assum drule >>
    disch_then (qspec_then ‘nt’ mp_tac) >>
    impl_tac >- gs [] >>
    strip_tac >>
    last_x_assum drule >>
    disch_then (qspecl_then [‘nt’, ‘ist’] mp_tac) >>
    impl_tac
    >- (
      gvs [assumptions_def] >>
      gs [nexts_ffi_def, input_rel_def] >>
      qpat_x_assum ‘state_rel _ _ _ t’ assume_tac >>
      gs [state_rel_def] >>
      pairarg_tac >> gs [] >>
      gs [input_time_rel_def] >>
      gs [input_time_eq_def, has_input_def] >>
      first_x_assum (qspec_then ‘0’ mp_tac) >>
      impl_tac
      >- (
        gs [] >>
        gs [input_rel_def, next_ffi_def]) >>
      gs [next_ffi_def] >>
      strip_tac >>
      cases_on ‘evaluate (always (nClks prog),t)’ >>
      gs [] >>
      drule evaluate_add_clock_eq >>
      gs [] >>
      disch_then (qspec_then ‘ck’ mp_tac) >>
      gs [] >>
      rpt strip_tac >>
      gs [sum_delays_def] >>
      gen_tac >>
      strip_tac >>
      first_x_assum (qspec_then ‘n' + 1’ mp_tac) >>
      first_x_assum (qspec_then ‘n' + 1’ mp_tac) >>
      gs [] >>
      strip_tac >>
      strip_tac >>
      gs [mem_read_ffi_results_def] >>
      rpt gen_tac >>
      strip_tac >>
      first_x_assum (qspec_then ‘i + 1’ mp_tac) >>
      gs [nexts_ffi_def] >>
      disch_then
      (qspec_then ‘t'' with ffi :=
                   (t''.ffi with ffi_state :=
                    (λn''. t.ffi.ffi_state (1 + (i + n''))))’ mp_tac) >>
      gs [] >>
      disch_then (qspec_then ‘t'''’ mp_tac) >>
      impl_tac
      >- (
        gs [] >>
        ‘t'' with
         ffi :=
         t''.ffi with
          ffi_state := (λn''. t.ffi.ffi_state (1 + (i + n''))) =
         t''’ by
          gs [state_component_equality, ffiTheory.ffi_state_component_equality] >>
        gs []) >>
      gs []) >>
    strip_tac >>
    first_x_assum (qspec_then ‘ck'’ assume_tac) >>
    qexists_tac ‘ck + ck'’ >> gs [] >>
    gs [input_io_events_rel_def] >>
    qexists_tac ‘1::ns’ >>
    rewrite_tac [decode_ios_def] >>
    gs [] >>
    gs [to_input_def, DROP_LENGTH_APPEND, decode_io_events_def] >>
    ‘LENGTH ios − 1 = SUM ns’ by gs [] >>
    simp []) >>
  gs [ffi_rels_def, ffi_rel_def, action_rel_def] >>
  first_x_assum drule >>
  disch_then (qspec_then ‘nt’ mp_tac) >>
  impl_tac >- gs [] >>
  strip_tac >>
  last_x_assum drule >>
  disch_then (qspecl_then [‘nt’, ‘ist’] mp_tac) >>
  impl_tac
  >- (
    gs [assumptions_def] >>
    cases_on ‘evaluate (always (nClks prog),t)’ >>
    gs [] >>
    drule evaluate_add_clock_eq >>
    gs [] >>
    disch_then (qspec_then ‘ck’ mp_tac) >>
    gs [] >>
    rpt strip_tac >>
    gs[sum_delays_def]) >>
  strip_tac >>
  first_x_assum (qspec_then ‘ck'’ assume_tac) >>
  qexists_tac ‘ck + ck'’ >> gs [] >>
  gs [output_io_events_rel_def] >>
  qexists_tac ‘1::ns’ >>
  rewrite_tac [decode_ios_def] >>
  gs [to_input_def, DROP_LENGTH_APPEND, decode_io_events_def] >>
  ‘LENGTH ios − 1 = SUM ns’ by gs [] >>
  simp []
QED

Theorem opt_mmap_empty_const:
  ∀t prog v n.
    FLOOKUP t.code (num_to_str (FST (ohd prog))) = SOME v ⇒
    OPT_MMAP (λa. eval t a)
             [Struct (emptyConsts n);
              Const 0w; Const 0w; Label (toString (FST (ohd prog)))] =
    SOME ([Struct (emptyVals n); ValWord 0w; ValWord 0w; ValLabel (toString (FST (ohd prog)))])
Proof
  rw [] >>
  gs [opt_mmap_eq_some] >>
  gs [eval_def] >>
  gs [eval_empty_const_eq_empty_vals, FDOM_FLOOKUP]
QED

Theorem eval_mkClks:
  ∀t st n.
    FLOOKUP t.locals «sysTime» = SOME (ValWord (n2w st)) ⇒
    OPT_MMAP (λa. eval t a) (mkClks «sysTime» n) =
    SOME (REPLICATE n (ValWord (n2w st)))
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [mkClks_def, opt_mmap_eq_some, eval_def]
QED


Theorem replicate_shape_one:
  ∀n.
    REPLICATE n One =
    MAP (λa. shape_of a) (emptyVals n)
Proof
  Induct >>
  gs [emptyVals_def, shape_of_def]
QED

Definition wf_prog_and_init_states_def:
  wf_prog_and_init_states prog st (t:('a,time_input) panSem$state) ⇔
    prog ≠ [] ∧ LENGTH (clksOf prog) ≤ 29 ∧
    st.location =  FST (ohd prog) ∧
    init_clocks st.clocks (clksOf prog) ∧
    code_installed t.code prog ∧
    FLOOKUP t.eshapes «panic» = SOME One ∧
    FLOOKUP t.code «start» =
    SOME ([], ta_controller (prog,st.waitTime)) ∧
    FLOOKUP t.code «start_controller» =
    SOME ([], start_controller (prog,st.waitTime)) ∧
    well_formed_code prog t.code ∧
    mem_config t.memory t.memaddrs t.be t.base_addr ∧
    mem_read_ffi_results (:α) t.ffi.ffi_state 1 ∧
    t.ffi =
    build_ffi (:'a) t.be (MAP explode (out_signals prog))
              t.ffi.ffi_state t.ffi.io_events ∧
    init_ffi t.ffi.ffi_state ∧
    input_time_rel t.ffi.ffi_state ∧
    FST (t.ffi.ffi_state 0) < dimword (:α) − 1 ∧
    time_seq t.ffi.ffi_state (dimword (:α)) ∧
    t.ffi.io_events = [] ∧
    good_dimindex (:'a) ∧
    ~MEM "get_time_input" (MAP explode (out_signals prog))
End

Theorem timed_automata_no_panic_correct_main:
  ∀prog labels st sts (t:('a,time_input) panSem$state).
    steps prog labels
          (dimword (:α) - 1) (FST (t.ffi.ffi_state 0)) st sts ∧
    no_panic labels ∧ byte_align t.base_addr = t.base_addr ∧
    wf_prog_and_init_states prog st t ∧
    ffi_rels_after_init prog labels st t ∧
    sum_delays (:α) labels (next_ffi t.ffi.ffi_state) ⇒
    ∃io ios ns.
      semantics t «start» = Terminate Success (io::ios) ∧
      LENGTH labels = LENGTH ns ∧
      SUM ns + 1 = LENGTH ios ∧
      decode_ios (:α) t.be labels ns
                 (io::TAKE (SUM ns) ios)
Proof
  rw [wf_prog_and_init_states_def, no_panic_def] >>
  ‘∃ck t' io ios ns.
     evaluate
     (TailCall (Label «start» ) [],t with clock := t.clock + ck) =
     (SOME (Return (ValWord 0w)),t') ∧
     t'.ffi.io_events = t.ffi.io_events ++ io::ios ∧
     t'.base_addr = t.base_addr ∧
     LENGTH labels' = LENGTH ns ∧
     SUM ns + 1 = LENGTH ios ∧
     decode_ios (:α) t.be labels' ns
                (io::TAKE (SUM ns) ios)’ by (
    ‘∃bytes.
       read_bytearray t.base_addr (w2n (ffiBufferSize:'a word))
                      (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes’ by (
      match_mp_tac read_bytearray_some_bytes_for_ffi >>
      rgs [] >>
      rgs [mem_config_def]) >>
    qabbrev_tac
    ‘nt =
     t with
       <|locals := locals_before_start_ctrl prog st.waitTime (t.ffi.ffi_state 0) t.base_addr;
         memory := mem_call_ffi (:α) t.memory t.memaddrs t.be t.base_addr t.ffi.ffi_state;
         clock := t.clock; ffi := ffi_call_ffi (:α) t.be t.ffi bytes|>’ >>
    ‘∃ck t' ns ios.
       evaluate (always (nClks prog),nt with clock := nt.clock + ck) =
       (SOME (Return (ValWord 0w)),t') ∧
       t'.ffi.io_events = nt.ffi.io_events ++ ios ∧
       LENGTH labels' = LENGTH ns ∧ SUM ns + 1 = LENGTH ios ∧
       (t'.be ⇔ nt.be) ∧ t'.base_addr = nt.base_addr ∧
       decode_ios (:α) t'.be labels' ns
                  (LAST nt.ffi.io_events::TAKE (SUM ns) ios)’ by (
      match_mp_tac steps_io_event_no_panic_thm >>
      MAP_EVERY qexists_tac [‘FST (t.ffi.ffi_state 0)’, ‘st’, ‘sts’,
                             ‘(FST (t.ffi.ffi_state 0))’] >>
      rgs [no_panic_def] >>
      conj_tac
      >- (
        unabbrev_all_tac >>
        rgs [assumptions_def, locals_before_start_ctrl_def] >> rveq >>
        conj_tac
        (* state_rel *)
        >- (
          rgs [state_rel_def] >>
          pairarg_tac >> rgs [] >>
          rgs [FLOOKUP_UPDATE, ffi_call_ffi_def, next_ffi_def, init_ffi_def,
              ffi_vars_def, time_vars_def] >>
          conj_tac
          >- (
            rgs [equivs_def, FLOOKUP_UPDATE] >>
            cases_on ‘st.waitTime’ >> rgs [active_low_def]) >>
          conj_tac
          >- (
            rgs [mem_call_ffi_def, mem_config_def] >>
            conj_tac >> (
              fs [] >>
              match_mp_tac write_bytearray_update_byte >>
              qspec_then ‘t.base_addr’ assume_tac byte_aligned_ba_step>>
              rgs [good_dimindex_def,byte_align_aligned,bytes_in_word_def] >>
              rgs [byte_align_def, byte_aligned_def, align_def, aligned_def, bytes_in_word_def] >>
              rgs [dimword_def] >>
              EVAL_TAC >>
              rveq >> rgs [] >>
              EVAL_TAC)) >>
          conj_tac
          >- (
            rgs [defined_clocks_def, init_clocks_def] >>
            rgs [EVERY_MEM]) >>
          conj_tac
          >- rgs [build_ffi_def, ffiTheory.ffi_state_component_equality] >>
          conj_tac
          >- (
            rgs [input_time_rel_def] >>
            rw [] >>
            last_x_assum (qspec_then ‘n + 1’ mp_tac) >>
            rgs []) >>
          conj_tac
          >- (
            rgs [time_seq_def] >>
            rw [] >>
            rgs [] >>
            cases_on ‘n’ >> rgs []
            >- (
              first_x_assum (qspec_then ‘1’ mp_tac) >>
              rgs []) >>
            first_x_assum (qspec_then ‘SUC (SUC n')’ mp_tac) >>
            rgs [ADD1]) >>
          rgs [clocks_rel_def, FLOOKUP_UPDATE] >>
          qexists_tac ‘REPLICATE (nClks prog) tm’ >>
          rgs [map_replicate, timeLangTheory.nClks_def] >>
          rgs [clkvals_rel_def, EVERY_MEM, init_clocks_def] >>
          rgs [GSYM MAP_K_REPLICATE] >>
          rgs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
          rw [] >>
          qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,ys))’ >>
          ‘EL n (ZIP (xs,ys)) = (EL n xs, EL n ys)’ by (
            match_mp_tac EL_ZIP >>
            unabbrev_all_tac >>
            rgs []) >>
          unabbrev_all_tac >>
          rgs [] >>
          rgs [MEM_EL] >>
          last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
          impl_tac >- metis_tac [] >>
          strip_tac >>
          rgs [EL_MAP]) >>
        rgs [init_ffi_def, ffi_call_ffi_def, next_ffi_def] >>
        (* event_inv *)
        conj_tac
        >- rgs [event_inv_def, FLOOKUP_UPDATE] >>
        rgs [task_ret_defined_def] >>
        rgs [FLOOKUP_UPDATE, emptyVals_def]) >>
      unabbrev_all_tac >>
      rgs [ffi_rels_after_init_def] >>
      qmatch_asmsub_abbrev_tac ‘ffi_rels _ _ _ tt'’ >>
      qmatch_goalsub_abbrev_tac ‘ffi_rels _ _ _ tt’ >>
      ‘tt' = tt’ by (
        unabbrev_all_tac >>
        rgs [state_component_equality]) >>
      rgs [ffi_call_ffi_def]) >>
    qexists_tac ‘ck + 2’ >>
    rw [] >>
    once_rewrite_tac [evaluate_def] >>
    rgs [] >>
    rgs [eval_def, OPT_MMAP_def, lookup_code_def, dec_clock_def, FUPDATE_LIST] >>
    (* qpat_x_assum ‘FLOOKUP t.code _ = _’  kall_tac >> *)
    (* ta_controller *)
    fs [ta_controller_def, panLangTheory.decs_def] >>
    once_rewrite_tac [evaluate_def] >>
    rgs [eval_def] >>
    once_rewrite_tac [evaluate_def] >>
    rgs [eval_def] >>
    pairarg_tac >> gvs [] >>
    pairarg_tac >> gvs [] >>
    pop_assum mp_tac >>
    rgs [panLangTheory.nested_seq_def] >>
    once_rewrite_tac [evaluate_def] >>
    rgs [] >>
    pairarg_tac >> gvs [] >>
    pop_assum mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    gvs [eval_def] >>
    rgs [eval_def, OPT_MMAP_def, lookup_code_def, dec_clock_def, FUPDATE_LIST] >>
    qpat_x_assum ‘FLOOKUP t.code _ = _’  kall_tac >>
    qpat_x_assum ‘FLOOKUP t.code _ = _’  kall_tac >>
    (* start contoller *)
    fs [start_controller_def, panLangTheory.decs_def] >>
    once_rewrite_tac [evaluate_def] >>
    rgs [eval_def] >>
    ‘∃v1. FLOOKUP t.code (num_to_str (FST (ohd prog))) = SOME v1’ by (
      cases_on ‘prog’ >>
      rgs [ohd_def, code_installed_def] >>
      cases_on ‘h’ >> rgs [] >> metis_tac []) >>
    rgs [] >>
    pairarg_tac >> rgs [] >>
    pop_assum mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘eval tt q’ >>
    ‘eval tt q =
     SOME (ValWord (
            case st.waitTime of
            | NONE => 1w
            | SOME _ => (0w:'a word)))’ by (
      unabbrev_all_tac >> rgs [] >>
      TOP_CASE_TAC >> rgs [eval_def]) >>
    unabbrev_all_tac >> rgs [] >>
    rgs [] >>
    pairarg_tac >> rgs [] >>
    rgs [evaluate_def, eval_def] >>
    rpt (pairarg_tac >> rgs []) >>
    strip_tac >> rveq >> rgs [] >>
    qmatch_asmsub_abbrev_tac ‘eval tt _’ >>
    ‘t.code =  tt.code’ by (
      unabbrev_all_tac >> rgs []) >>
    fs [] >>
    drule opt_mmap_empty_const >>
    disch_then (qspec_then ‘nClks prog’ assume_tac) >>
    rgs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    pairarg_tac >>
    unabbrev_all_tac >> rgs [] >>
    rveq >> rgs [] >>
    qmatch_asmsub_abbrev_tac ‘eval tt _’ >>
    rgs [eval_empty_const_eq_empty_vals] >>
    pairarg_tac >>
    unabbrev_all_tac >> rgs [] >>
    rveq >> rgs [] >>
    rgs [FLOOKUP_UPDATE] >>
    (* Decs are completed *)
    rgs [panLangTheory.nested_seq_def] >>
    pop_assum mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    rgs [] >>
    pairarg_tac >> rveq >> rgs [] >>
    fs [check_input_time_def] >>
    fs [panLangTheory.nested_seq_def] >>
    rewrite_tac [Once evaluate_def] >>
    pop_assum mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    rgs [] >>
    pairarg_tac >> rveq >> rgs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (_, nt)’ >>
    ‘∃bytes.
       read_bytearray nt.base_addr (w2n (ffiBufferSize:'a word))
                      (mem_load_byte nt.memory nt.memaddrs nt.be) = SOME bytes’ by (
      match_mp_tac read_bytearray_some_bytes_for_ffi >>
      rgs [] >>
      unabbrev_all_tac >> rgs [mem_config_def]) >>
    drule evaluate_ext_call >>
    disch_then (qspecl_then [‘MAP explode (out_signals prog)’,‘bytes’] mp_tac) >>
    rgs [] >>
    impl_tac
    >- (
      unabbrev_all_tac >> rgs [ffi_vars_def, FLOOKUP_UPDATE]) >>
    strip_tac >> rveq >> rgs [] >>
    pop_assum kall_tac >>
    unabbrev_all_tac >> rgs [] >>
    (* reading systime *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
    ‘nt.memory nt.base_addr = Word (n2w (FST(t.ffi.ffi_state 0)))’ by (
      fs [Abbr ‘nt’] >>
      rgs [mem_call_ffi_def] >>
      qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
      rgs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, nt) = (_, ft)’ >>
      first_x_assum (qspecl_then [‘nt’, ‘ft’] mp_tac) >>
      impl_tac
      >- (
        rgs [Abbr ‘ft’, Abbr ‘nt’, nexts_ffi_def, ETA_AX] >> metis_tac []) >>
      strip_tac >>
      rgs [Abbr ‘ft’, nexts_ffi_def, init_ffi_def]) >>
    drule evaluate_assign_load >>
    rgs [] >>
    disch_then (qspecl_then
                [‘t.base_addr’, ‘0w’,
                 ‘n2w (FST (t.ffi.ffi_state 0))’] mp_tac) >>
    impl_tac
    >- (unabbrev_all_tac >> rgs [FLOOKUP_UPDATE, mem_config_def]) >>
    strip_tac >> unabbrev_all_tac >> rveq >> rgs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    (* reading input to the variable event *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «event» _, nnt)’ >>
    ‘nnt.memory (nnt.base_addr +  bytes_in_word) =
     Word (n2w (SND(t.ffi.ffi_state 0)))’ by (
      fs [Abbr ‘nnt’] >>
      qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
      rgs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, nt) = (_, ft)’ >>
      last_x_assum (qspecl_then [‘nt’, ‘ft’] mp_tac) >>
      impl_tac
      >- (gs [Abbr ‘ft’, Abbr ‘nt’, nexts_ffi_def, ETA_AX] >> metis_tac []) >>
      strip_tac >>
      rgs [Abbr ‘ft’, nexts_ffi_def, init_ffi_def]) >>
    rgs [] >>
    drule evaluate_assign_load_next_address >>
    rgs [] >>
    disch_then (qspecl_then
                [‘t.base_addr’,
                 ‘n2w (SND (t.ffi.ffi_state 0))’] mp_tac) >>
    impl_tac
    >- (unabbrev_all_tac >> rgs [FLOOKUP_UPDATE, mem_config_def]) >>
    strip_tac >>
    unabbrev_all_tac >>
    rgs [] >> rveq >> rgs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    (* isInput *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    drule evaluate_assign_compare_next_address >>
    rgs [] >>
    disch_then (qspecl_then [‘t.base_addr’] mp_tac) >>
    impl_tac
    >- (
      rgs [FLOOKUP_UPDATE, mem_call_ffi_def] >>
      qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
      rgs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, nt) = (_, ft)’ >>
      first_x_assum (qspecl_then [‘nt’, ‘ft’] mp_tac) >>
      impl_tac
      >- (
        rgs [Abbr ‘ft’, Abbr ‘nt’, nexts_ffi_def, ETA_AX] >> metis_tac []) >>
      strip_tac >>
      rgs [Abbr ‘ft’, nexts_ffi_def, init_ffi_def, mem_config_def]) >>
    strip_tac >> rveq >> rgs [] >>
    pop_assum kall_tac >>
    (* If statement *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    drule evaluate_if_compare_sys_time >>
    disch_then (qspec_then ‘FST (t.ffi.ffi_state 0)’ mp_tac) >>
    impl_tac
    >- (
      unabbrev_all_tac >>
      rgs [FLOOKUP_UPDATE]) >>
    strip_tac >> rveq >> rgs [] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    strip_tac >> fs [] >>
    rveq >> rgs [] >>
    pairarg_tac >> rveq >> rgs [] >>
    rgs [eval_def, FLOOKUP_UPDATE] >>
    qmatch_asmsub_abbrev_tac ‘eval nt _’ >>
    ‘FLOOKUP nt.locals «sysTime» = SOME (ValWord (n2w (FST (t.ffi.ffi_state 0))))’ by
      rgs [Abbr ‘nt’,FLOOKUP_UPDATE] >>
    drule eval_mkClks >>
    disch_then (qspec_then ‘nClks prog’ assume_tac) >>
    fs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    fs [is_valid_value_def, FLOOKUP_UPDATE] >>
    fs [panSemTheory.shape_of_def] >>
    rgs [replicate_shape_one] >>
    unabbrev_all_tac >> rveq >> rgs[] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    pairarg_tac >> rveq >> rgs [] >>
    pop_assum mp_tac >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    qmatch_goalsub_abbrev_tac ‘eval tt q’ >>
    ‘eval tt q =
     SOME (ValWord (n2w (
                     case st.waitTime of
                     | NONE => FST (t.ffi.ffi_state 0)
                     | SOME n => FST (t.ffi.ffi_state 0) + n)))’ by (
      cases_on ‘st.waitTime’ >>
      unabbrev_all_tac >>
      rgs [eval_def, FLOOKUP_UPDATE, OPT_MMAP_def,
          wordLangTheory.word_op_def, word_add_n2w]) >>
    rgs [is_valid_value_def, FLOOKUP_UPDATE, shape_of_def] >>
    strip_tac >> rveq >> rgs [] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> rveq >> rgs [] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    (* until always *)
    rgs [locals_before_start_ctrl_def] >>
    strip_tac >>
    gvs [empty_locals_def] >>
    rgs [ffi_call_ffi_def] >>
    gvs [shape_of_def, set_var_def] >>
    strip_tac >> gvs [] >>
    strip_tac >> gvs [panLangTheory.size_of_shape_def] >>
    qexists_tac ‘ns’ >> gvs []) >>
  rgs [semantics_def] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  rw []
  >- (
    cases_on
    ‘evaluate (TailCall (Label «start» ) [],t with clock := k')’ >>
    rgs [] >>
    cases_on ‘q = SOME TimeOut’ >>
    rgs [] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    drule evaluate_add_clock_eq >>
    rgs [] >>
    disch_then (qspec_then ‘k'’ assume_tac) >>
    rgs [] >>
    strip_tac >>
    strip_tac >>
    strip_tac >>
    strip_tac >>
    drule evaluate_add_clock_eq >>
    rgs [] >>
    disch_then (qspec_then ‘ck + t.clock’ assume_tac) >>
    rgs [])
  >- (
    rgs [] >>
    first_x_assum (qspec_then ‘ck + t.clock’ assume_tac) >> rgs [] >>
    cases_on ‘r = SOME TimeOut’ >>
    rgs [] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    drule evaluate_add_clock_eq >>
    rgs [] >>
    disch_then (qspec_then ‘k’ assume_tac) >>
    rgs [] >>
    strip_tac >>
    strip_tac >>
    strip_tac >>
    drule evaluate_add_clock_eq >>
    rgs [] >>
    disch_then (qspec_then ‘ck + t.clock’ assume_tac) >>
    rgs [] >> gvs [] >>
    MAP_EVERY qexists_tac [‘io’, ‘ios’, ‘ns’] >>
    gvs [state_component_equality])
  >- (
    cases_on
    ‘evaluate (TailCall (Label «start» ) [],t with clock := k)’ >>
    rgs [] >>
    cases_on ‘q = SOME TimeOut’ >>
    rgs [] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    drule evaluate_add_clock_eq >>
    rgs [] >>
    disch_then (qspec_then ‘k’ assume_tac) >>
    rgs [] >>
    strip_tac >>
    strip_tac >>
    drule evaluate_add_clock_eq >>
    rgs [] >>
    disch_then (qspec_then ‘ck + t.clock’ assume_tac) >>
    rgs []) >>
  rgs [] >>
  qexists_tac ‘ck + t.clock’ >>
  rgs []
QED

Theorem take_one_less_length_eq_front:
  ∀xs .
    xs ≠ [] ⇒
    TAKE (LENGTH xs − 1) xs = FRONT xs
Proof
  Induct >>
  rw [] >>
  rgs [FRONT_DEF] >>
  cases_on ‘xs’ >> gvs []
QED


Theorem from_take_sum_to_front:
  ∀xs ns.
    SUM ns + 1 = LENGTH xs ⇒
    TAKE (SUM ns) xs = FRONT xs
Proof
  Induct >>
  rw [] >>
  rgs [ADD1] >>
  cases_on ‘ns’ >> rgs [] >>
  rgs [TAKE_def] >>
  cases_on ‘xs’
  >- gvs [] >>
  qmatch_goalsub_abbrev_tac ‘LENGTH xs’ >>
  ‘TAKE (LENGTH xs − 1) xs = FRONT xs’ by (
    match_mp_tac take_one_less_length_eq_front >>
    unabbrev_all_tac >> rgs []) >>
  unabbrev_all_tac >> rgs []
QED

Theorem timed_automata_no_panic_correct:
  ∀prog labels st sts (t:('a,time_input) panSem$state).
    steps prog labels
          (dimword (:α) - 1) (FST (t.ffi.ffi_state 0)) st sts ∧
    no_panic labels ∧ byte_align t.base_addr = t.base_addr ∧
    wf_prog_and_init_states prog st t ∧
    ffi_rels_after_init prog labels st t ∧
    sum_delays (:α) labels (next_ffi t.ffi.ffi_state) ⇒
    ∃io ios ns.
      semantics t «start» = Terminate Success (io::ios) ∧
      LENGTH labels = LENGTH ns ∧
      SUM ns + 1 = LENGTH ios ∧
      decode_ios (:α) t.be labels ns (io::FRONT ios)
Proof
  rw [] >>
  drule_all timed_automata_no_panic_correct_main >>
  strip_tac >>
  rgs [] >>
  qexists_tac ‘ns’ >> rgs [from_take_sum_to_front]
QED


Theorem timed_automata_no_panic_functional_correct:
  ∀k prog or st sts labels (t:('a,time_input) panSem$state).
    timeFunSem$eval_steps k prog
               (dimword (:α) - 1) (FST (t.ffi.ffi_state 0))
               or st = SOME (labels, sts) ∧
    no_panic labels ∧ byte_align t.base_addr = t.base_addr ∧
    wf_prog_and_init_states prog st t ∧
    ffi_rels_after_init prog labels st t ∧
    sum_delays (:α) labels (next_ffi t.ffi.ffi_state) ⇒
    ∃io ios ns.
      semantics t «start» = Terminate Success (io::ios) ∧
      LENGTH labels = LENGTH ns ∧
      SUM ns + 1 = LENGTH ios ∧
      decode_ios (:α) t.be labels ns (io::FRONT ios)
Proof
  rw [] >>
  dxrule eval_steps_imp_steps >>
  strip_tac >>
  metis_tac [timed_automata_no_panic_correct]
QED


Theorem io_trace_impl_eval_steps:
  ∀prog st (t:('a,time_input) panSem$state) or k.
    wf_prog_init_states prog or k st t ∧
    ffi_rels_after_init prog
                        (labels_of k prog (dimword (:α) - 1) (systime_at t) or st) st t ∧
    no_panic (labels_of k prog (dimword (:α) - 1) (systime_at t) or st) ∧
    byte_align t.base_addr = t.base_addr ∧
    sum_delays (:α) (labels_of k prog (dimword (:α) - 1) (systime_at t) or st)
               (next_ffi t.ffi.ffi_state) ⇒
    ∃lbls sts io ios ns.
      timeFunSem$eval_steps k prog (dimword (:α) - 1) (systime_at t) or st =
      SOME (lbls, sts) ∧
      semantics t «start» = Terminate Success (io::ios) ∧
      LENGTH lbls = LENGTH ns ∧ SUM ns + 1 = LENGTH ios ∧
      decode_ios (:α) t.be lbls ns (io::FRONT ios)
Proof
  rw [] >>
  rgs [wf_prog_init_states_def, systime_at_def] >>
  ‘∃lbls sts.
     timeFunSem$eval_steps k prog (dimword (:α) − 1)
                           (FST (t.ffi.ffi_state 0)) or st = SOME (lbls,sts)’ by (
    rgs [GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >>
    cases_on ‘(timeFunSem$eval_steps k prog (dimword (:α) − 1)
               (FST (t.ffi.ffi_state 0)) or st)’ >>
    rgs [IS_SOME_DEF] >>
    cases_on ‘x’ >> rgs []) >>
  rgs [labels_of_def] >>
  metis_tac [timed_automata_no_panic_functional_correct,
             wf_prog_and_init_states_def]
QED


Definition has_panic_def:
  has_panic lbls ⇔
  ∃lbl.
    MEM lbl lbls ∧
    (lbl = LPanic (PanicTimeout) ∨
     (∃is. lbl = LPanic is))
End

Definition panic_at_def:
  (panic_at [] = NONE) ∧
  (panic_at (lbl::lbls) =
   case lbl of
   | LPanic p => SOME p
   | _ => panic_at lbls)
End


Definition until_panic_def:
  (until_panic [] = []) ∧
  (until_panic (lbl::lbls) =
   case lbl of
   | LPanic p => []
   | _ => lbl::until_panic lbls)
End

Definition uptil_panic_def:
  (uptil_panic [] = []) ∧
  (uptil_panic (lbl::lbls) =
   case lbl of
   | LPanic p => [LPanic p]
   | _ => lbl::uptil_panic lbls)
End

Definition slice_labels_def:
  (slice_labels [] = []) ∧
  (slice_labels (lbl::lbls) =
   case lbl of
   | LPanic p =>
       (case p of
        | PanicTimeout => []
        | _ => [LPanic p])
  | _ => lbl::slice_labels lbls)
End


Definition sum_delays_until_panic_def:
  sum_delays_until_panic (:α) lbls (ffi:time_input) ⇔
    SUM (MAP (λlbl.
               case lbl of
               | LDelay d => d
               | _ => 0) lbls) + FST (ffi 0) < dimword (:α) − 2
End


Theorem steps_io_event_uptil_panic_thm:
  ∀labels prog n st sts (t:('a,time_input) panSem$state) ist.
    steps prog labels (dimword (:α) - 1) n st sts ∧
    has_panic labels ∧
    assumptions prog n st t ∧
    ffi_rels prog (uptil_panic labels) st t ist ∧
    sum_delays_until_panic (:α) (until_panic labels) t.ffi.ffi_state ⇒
    ∃ck t' ns ios.
      evaluate (time_to_pan$always (nClks prog), t with clock := t.clock + ck) =
      (SOME (Exception «panic» (ValWord 0w)),t') ∧
      t'.ffi.io_events = t.ffi.io_events ++ ios ∧
      LENGTH (slice_labels labels) = LENGTH ns ∧
      SUM ns = LENGTH ios ∧
      t'.be = t.be ∧
      decode_ios (:α) t'.be (slice_labels labels) ns (LAST t.ffi.io_events::ios)
Proof
  rw [] >>
  rgs [] >>
  drule_all steps_thm >>
  disch_then (qspec_then ‘ist’ mp_tac) >>
  strip_tac >>
  rpt (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [‘ist’, ‘t’, ‘sts’, ‘st’, ‘n’, ‘prog’, ‘labels'’] >>
  Induct
  >- (
    rw [] >>
    rgs [has_panic_def]) >>
  rw [] >>
  ‘LENGTH sts = LENGTH (h::labels')’ by
    metis_tac [steps_sts_length_eq_lbls] >>
  cases_on ‘sts’ >>
  fs [] >>
  ‘n = FST (t.ffi.ffi_state 0)’ by
    rgs [assumptions_def] >>
  rveq >> rgs [] >>
  rgs [evaluations_def, steps_def] >>
  cases_on ‘h’ >> rgs []
  >- (
    rgs [uptil_panic_def, ffi_rels_def, ffi_rel_def, slice_labels_def, panic_at_def] >>
    first_x_assum drule >>
    rgs [] >>
    strip_tac >>
    last_x_assum drule >>
    disch_then (qspecl_then [‘nt’, ‘ist’] mp_tac) >>
    impl_tac
    >- (
      conj_tac
      >- (gvs [has_panic_def] >> metis_tac []) >>
      rgs [assumptions_def] >>
      rgs [nexts_ffi_def, delay_rep_def] >>
      conj_tac
      >- (
        first_x_assum match_mp_tac >>
        metis_tac []) >>
      gvs [until_panic_def, sum_delays_until_panic_def]) >>
    strip_tac >>
    first_x_assum (qspec_then ‘ck'’ assume_tac) >>
    qexists_tac ‘ck + ck'’ >> rgs [] >>
    rgs [delay_io_events_rel_def] >>
    qexists_tac ‘cycles::ns’ >>
    rewrite_tac [decode_ios_def] >>
    rgs [] >>
    TOP_CASE_TAC
    >- (
      rgs [mk_ti_events_def, gen_ffi_states_def] >>
      rgs [delay_rep_def] >>
      drule decode_ios_length_eq_sum >>
      rgs []) >>
    conj_asm1_tac
    >-  rgs [mk_ti_events_def, gen_ffi_states_def] >>
    conj_asm1_tac
    >- rgs [TAKE_SUM] >>
    qmatch_asmsub_abbrev_tac ‘decode_ios _ _ _ ns nios’ >>
    qmatch_goalsub_abbrev_tac ‘decode_ios _ _ _ ns nios'’ >>
    ‘nios = nios'’ by (
      rgs [Abbr ‘nios’, Abbr ‘nios'’] >>
      qmatch_goalsub_abbrev_tac ‘DROP _ (xs ++ _)’ >>
      ‘cycles = LENGTH xs’ by
        rgs [Abbr ‘xs’, mk_ti_events_def, gen_ffi_states_def] >>
      rgs [TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
      rgs [DROP_APPEND] >>
      ‘LENGTH xs − 1 − LENGTH xs = 0’ by rgs [] >>
      simp [] >>
      pop_assum kall_tac >>
      ‘DROP (LENGTH xs − 1) xs = [LAST xs]’ by (
        match_mp_tac drop_length_eq_last >>
        CCONTR_TAC >>
        gvs []) >>
      rgs [] >>
      ‘cycles = LENGTH xs’ by gvs [] >>
      cases_on ‘xs’ >- rgs [] >>
      simp [LAST_APPEND_CONS] >> gvs [] >>
      ‘LENGTH t'³' − SUC (LENGTH t'³') = 0’ by rgs [] >>
      simp [] >>
      conj_asm1_tac
      >- (
        rgs [DROP_LENGTH_NIL, TAKE_LENGTH_APPEND, LAST_CONS_cond] >>
        cases_on ‘t'''’ >> gvs []) >>
      ‘SUC (LENGTH t'³') − (SUC (LENGTH t'³') + 1)= 0’ by rgs [] >>
      simp []) >>
    qpat_x_assum ‘obs_ios_are_label_delay _ _ _’ mp_tac >>
    rgs [obs_ios_are_label_delay_def] >>
    strip_tac >>
    pop_assum mp_tac >>
    impl_tac
    >- (
      CCONTR_TAC >>
      rgs [DROP_LENGTH_APPEND, mk_ti_events_def, gen_ffi_states_def, decode_io_events_def] >>
      rgs [ZIP_EQ_NIL]) >>
    strip_tac >>
    rgs [] >>
    qmatch_goalsub_abbrev_tac ‘TAKE _ (xs ++ _)’ >>
    ‘TAKE cycles (xs ++ ios) =
     xs’ by (
      ‘cycles = LENGTH xs’ by
         rgs [Abbr ‘xs’, mk_ti_events_def, gen_ffi_states_def] >>
      simp [] >>
      rgs [TAKE_LENGTH_APPEND]) >>
    rgs [Abbr ‘xs’, DROP_LENGTH_APPEND])
  >- (
    cases_on ‘i’
    >- (
      rgs [uptil_panic_def, ffi_rels_def, ffi_rel_def, action_rel_def, slice_labels_def, panic_at_def] >>
      first_x_assum drule >>
      disch_then (qspec_then ‘nt’ mp_tac) >>
      impl_tac >- rgs [] >>
      strip_tac >>
      last_x_assum drule >>
      disch_then (qspecl_then [‘nt’, ‘ist’] mp_tac) >>
      impl_tac
      >- (
        conj_tac
        >- (gvs [has_panic_def] >> metis_tac []) >>
        gvs [assumptions_def] >>
        rgs [nexts_ffi_def, input_rel_def] >>
        qpat_x_assum ‘state_rel _ _ _ t’ assume_tac >>
        rgs [state_rel_def] >>
        pairarg_tac >> rgs [] >>
        rgs [input_time_rel_def] >>
        rgs [input_time_eq_def, has_input_def] >>
        first_x_assum (qspec_then ‘0’ mp_tac) >>
        impl_tac
        >- (
          rgs [] >>
          rgs [input_rel_def, next_ffi_def]) >>
        rgs [next_ffi_def] >>
        strip_tac >>
        gvs [until_panic_def, sum_delays_until_panic_def]) >>
      strip_tac >>
      first_x_assum (qspec_then ‘ck'’ assume_tac) >>
      qexists_tac ‘ck + ck'’ >> rgs [] >>
      rgs [input_io_events_rel_def] >>
      qexists_tac ‘1::ns’ >>
      rewrite_tac [decode_ios_def] >>
      rgs [] >>
      rgs [to_input_def, DROP_LENGTH_APPEND, decode_io_events_def] >>
      ‘LENGTH ios − 1 = SUM ns’ by rgs [] >>
      simp []) >>
    rgs [uptil_panic_def, ffi_rels_def, ffi_rel_def, action_rel_def, slice_labels_def, panic_at_def] >>
    first_x_assum drule >>
    disch_then (qspec_then ‘nt’ mp_tac) >>
    impl_tac >- rgs [] >>
    strip_tac >>
    last_x_assum drule >>
    disch_then (qspecl_then [‘nt’, ‘ist’] mp_tac) >>
    impl_tac
    >- (
      conj_tac
      >- (gvs [has_panic_def] >> metis_tac []) >>
      rgs [assumptions_def] >>
      gvs [until_panic_def, sum_delays_until_panic_def]) >>
    strip_tac >>
    first_x_assum (qspec_then ‘ck'’ assume_tac) >>
    qexists_tac ‘ck + ck'’ >> rgs [] >>
    rgs [output_io_events_rel_def] >>
    qexists_tac ‘1::ns’ >>
    rewrite_tac [decode_ios_def] >>
    rgs [to_input_def, DROP_LENGTH_APPEND, decode_io_events_def] >>
    ‘LENGTH ios − 1 = SUM ns’ by rgs [] >>
    simp []) >>
  cases_on ‘p’ >> gvs []
  >- (
    gvs [slice_labels_def, until_panic_def, panic_at_def,
         sum_delays_until_panic_def, uptil_panic_def] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    impl_tac
    >- gvs [ffi_rels_def, ffi_rel_def, panic_rel_def] >>
    strip_tac >> gvs [] >>
    strip_tac >>
    first_x_assum (qspec_then ‘0’ assume_tac) >>
    qexists_tac ‘ck’ >>
    qexists_tac ‘nt’ >>
    rgs [state_component_equality, ffiTheory.ffi_state_component_equality] >>
    (* cases_on ‘t.ffi.io_events’ >> *)
    gvs [decode_ios_def]) >>
  gvs [slice_labels_def, until_panic_def, panic_at_def,
       sum_delays_until_panic_def, uptil_panic_def] >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  impl_tac
  >- gvs [ffi_rels_def, ffi_rel_def, panic_rel_def] >>
  strip_tac >> gvs [] >>
  strip_tac >>
  first_x_assum (qspec_then ‘0’ assume_tac) >>
  qexists_tac ‘ck’ >>
  qexists_tac ‘nt’ >>
  rgs [state_component_equality, ffiTheory.ffi_state_component_equality] >>
  gvs [input_io_events_rel_def] >>
  qexists_tac ‘[1]’ >>
  gvs [] >>
  rewrite_tac [decode_ios_def] >>
  rgs [] >>
  rgs [to_input_def, DROP_LENGTH_APPEND, decode_io_events_def]
QED

Theorem timed_automata_until_panic_correct:
  ∀prog labels st sts (t:('a,time_input) panSem$state).
    steps prog labels
          (dimword (:α) - 1) (FST (t.ffi.ffi_state 0)) st sts ∧
    has_panic labels ∧ byte_align t.base_addr = t.base_addr ∧
    wf_prog_and_init_states prog st t ∧
    ffi_rels_after_init prog (uptil_panic labels) st t ∧
    sum_delays_until_panic (:α) (until_panic labels) (next_ffi t.ffi.ffi_state) ⇒
    ∃io ios ns.
      semantics t «start» = Terminate Success (io::ios) ∧
      LENGTH (slice_labels labels) = LENGTH ns ∧
      SUM ns = LENGTH ios ∧
      decode_ios (:α) t.be (slice_labels labels) ns (io::ios)
Proof
  rw [wf_prog_and_init_states_def] >>
  ‘∃ck t' io ios ns.
     evaluate
     (TailCall (Label «start» ) [],t with clock := t.clock + ck) =
     (SOME (Return (ValWord 1w)),t') ∧
     t'.ffi.io_events = t.ffi.io_events ++ io::ios ∧
     byte_align t.base_addr = t.base_addr ∧
     LENGTH (slice_labels labels') = LENGTH ns ∧
     SUM ns = LENGTH ios ∧
     decode_ios (:α) t.be (slice_labels labels') ns (io::ios)’ by (
    ‘∃bytes.
       read_bytearray t.base_addr (w2n (ffiBufferSize:'a word))
                      (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes’ by (
      match_mp_tac read_bytearray_some_bytes_for_ffi >>
      rgs [] >>
      rgs [mem_config_def]) >>
    qabbrev_tac
    ‘nt =
     t with
       <|locals := locals_before_start_ctrl prog st.waitTime (t.ffi.ffi_state 0) t.base_addr;
         memory := mem_call_ffi (:α) t.memory t.memaddrs t.be t.base_addr t.ffi.ffi_state;
         clock := t.clock; ffi := ffi_call_ffi (:α) t.be t.ffi bytes|>’ >>
    ‘∃ck t' ns ios.
       evaluate (always (nClks prog),nt with clock := nt.clock + ck) =
       (SOME (Exception «panic» (ValWord 0w)),t') ∧
       t'.ffi.io_events = nt.ffi.io_events ++ ios ∧
       LENGTH (slice_labels labels') = LENGTH ns ∧
       SUM ns = LENGTH ios ∧
       (t'.be ⇔ nt.be) ∧
       decode_ios (:α) t'.be (slice_labels labels') ns (LAST nt.ffi.io_events::ios)’ by (
      match_mp_tac steps_io_event_uptil_panic_thm >>
      MAP_EVERY qexists_tac [‘FST (t.ffi.ffi_state 0)’, ‘st’, ‘sts’,
                             ‘(FST (t.ffi.ffi_state 0))’] >>
      rgs [] >>
      conj_tac
      >- (
        unabbrev_all_tac >>
        rgs [assumptions_def, locals_before_start_ctrl_def] >> rveq >>
        conj_tac
        (* state_rel *)
        >- (
          rgs [state_rel_def] >>
          pairarg_tac >> rgs [] >>
          rgs [FLOOKUP_UPDATE, ffi_call_ffi_def, next_ffi_def, init_ffi_def,
              ffi_vars_def, time_vars_def] >>
          conj_tac
          >- (
            rgs [equivs_def, FLOOKUP_UPDATE] >>
            cases_on ‘st.waitTime’ >> rgs [active_low_def]) >>
          conj_tac
          >- (
            rgs [mem_call_ffi_def, mem_config_def] >>
            conj_tac >> (
              fs [] >>
              match_mp_tac write_bytearray_update_byte >>
              qspec_then ‘t.base_addr’ assume_tac byte_aligned_ba_step>>
              rgs [good_dimindex_def,byte_align_aligned,bytes_in_word_def] >>
              rgs [byte_align_def, byte_aligned_def, align_def, aligned_def, bytes_in_word_def] >>
              rgs [dimword_def] >>
              EVAL_TAC >>
              rveq >> rgs [] >>
              EVAL_TAC)) >>
          conj_tac
          >- (
            rgs [defined_clocks_def, init_clocks_def] >>
            rgs [EVERY_MEM]) >>
          conj_tac
          >- rgs [build_ffi_def, ffiTheory.ffi_state_component_equality] >>
          conj_tac
          >- (
            rgs [input_time_rel_def] >>
            rw [] >>
            last_x_assum (qspec_then ‘n + 1’ mp_tac) >>
            rgs []) >>
          conj_tac
          >- (
            rgs [time_seq_def] >>
            rw [] >>
            rgs [] >>
            cases_on ‘n’ >> rgs []
            >- (
              first_x_assum (qspec_then ‘1’ mp_tac) >>
              rgs []) >>
            first_x_assum (qspec_then ‘SUC (SUC n')’ mp_tac) >>
            rgs [ADD1]) >>
          rgs [clocks_rel_def, FLOOKUP_UPDATE] >>
          qexists_tac ‘REPLICATE (nClks prog) tm’ >>
          rgs [map_replicate, timeLangTheory.nClks_def] >>
          rgs [clkvals_rel_def, EVERY_MEM, init_clocks_def] >>
          rgs [GSYM MAP_K_REPLICATE] >>
          rgs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
          rw [] >>
          qmatch_goalsub_abbrev_tac ‘EL _ (ZIP (xs,ys))’ >>
          ‘EL n (ZIP (xs,ys)) = (EL n xs, EL n ys)’ by (
            match_mp_tac EL_ZIP >>
            unabbrev_all_tac >>
            rgs []) >>
          unabbrev_all_tac >>
          rgs [] >>
          rgs [MEM_EL] >>
          last_x_assum (qspec_then ‘EL n (clksOf prog)’ mp_tac) >>
          impl_tac >- metis_tac [] >>
          strip_tac >>
          rgs [EL_MAP]) >>
        rgs [init_ffi_def, ffi_call_ffi_def, next_ffi_def] >>
        (* event_inv *)
        conj_tac
        >- rgs [event_inv_def, FLOOKUP_UPDATE] >>
        rgs [task_ret_defined_def] >>
        rgs [FLOOKUP_UPDATE, emptyVals_def]) >>
      unabbrev_all_tac >>
      rgs [ffi_rels_after_init_def] >>
      qmatch_asmsub_abbrev_tac ‘ffi_rels _ _ _ tt'’ >>
      qmatch_goalsub_abbrev_tac ‘ffi_rels _ _ _ tt’ >>
      ‘tt' = tt’ by (
        unabbrev_all_tac >>
        rgs [state_component_equality]) >>
      rgs [ffi_call_ffi_def]) >>
    qexists_tac ‘ck + 2’ >>
    rw [] >>
    once_rewrite_tac [evaluate_def] >>
    rgs [] >>
    rgs [eval_def, OPT_MMAP_def, lookup_code_def, dec_clock_def, FUPDATE_LIST] >>

    fs [ta_controller_def, panLangTheory.decs_def] >>
    once_rewrite_tac [evaluate_def] >>
    rgs [eval_def] >>
    once_rewrite_tac [evaluate_def] >>
    rgs [eval_def] >>
    pairarg_tac >> gvs [] >>
    pairarg_tac >> gvs [] >>
    pop_assum mp_tac >>
    rgs [panLangTheory.nested_seq_def] >>
    once_rewrite_tac [evaluate_def] >>
    rgs [] >>
    pairarg_tac >> gvs [] >>
    pop_assum mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    gvs [eval_def] >>
    rgs [eval_def, OPT_MMAP_def, lookup_code_def, dec_clock_def, FUPDATE_LIST] >>
    qpat_x_assum ‘FLOOKUP t.code _ = _’  kall_tac >>
    qpat_x_assum ‘FLOOKUP t.code _ = _’  kall_tac >>
    (* start contoller *)
    fs [start_controller_def, panLangTheory.decs_def] >>
    once_rewrite_tac [evaluate_def] >>
    rgs [eval_def] >>
    ‘∃v1. FLOOKUP t.code (num_to_str (FST (ohd prog))) = SOME v1’ by (
      cases_on ‘prog’ >>
      rgs [ohd_def, code_installed_def] >>
      cases_on ‘h’ >> rgs [] >> metis_tac []) >>
    rgs [] >>
    pairarg_tac >> rgs [] >>
    pop_assum mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    qmatch_goalsub_abbrev_tac ‘eval tt q’ >>
    ‘eval tt q =
     SOME (ValWord (
            case st.waitTime of
            | NONE => 1w
            | SOME _ => (0w:'a word)))’ by (
      unabbrev_all_tac >> rgs [] >>
      TOP_CASE_TAC >> rgs [eval_def]) >>
    unabbrev_all_tac >> rgs [] >>
    rgs [] >>
    pairarg_tac >> rgs [] >>
    rgs [evaluate_def, eval_def] >>
    rpt (pairarg_tac >> rgs []) >>
    strip_tac >> rveq >> rgs [] >>
    qmatch_asmsub_abbrev_tac ‘eval tt _’ >>
    ‘t.code =  tt.code’ by (
      unabbrev_all_tac >> rgs []) >>
    fs [] >>
    drule opt_mmap_empty_const >>
    disch_then (qspec_then ‘nClks prog’ assume_tac) >>
    rgs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    pairarg_tac >>
    unabbrev_all_tac >> rgs [] >>
    rveq >> rgs [] >>
    qmatch_asmsub_abbrev_tac ‘eval tt _’ >>
    rgs [eval_empty_const_eq_empty_vals] >>
    pairarg_tac >>
    unabbrev_all_tac >> rgs [] >>
    rveq >> rgs [] >>
    rgs [FLOOKUP_UPDATE] >>
    (* Decs are completed *)
    rgs [panLangTheory.nested_seq_def] >>
    pop_assum mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    rgs [] >>
    pairarg_tac >> rveq >> rgs [] >>
    fs [check_input_time_def] >>
    fs [panLangTheory.nested_seq_def] >>
    rewrite_tac [Once evaluate_def] >>
    pop_assum mp_tac >>
    once_rewrite_tac [evaluate_def] >>
    rgs [] >>
    pairarg_tac >> rveq >> rgs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (_, nt)’ >>
    ‘∃bytes.
       read_bytearray nt.base_addr (w2n (ffiBufferSize:'a word))
                      (mem_load_byte nt.memory nt.memaddrs nt.be) = SOME bytes’ by (
      match_mp_tac read_bytearray_some_bytes_for_ffi >>
      rgs [] >>
      unabbrev_all_tac >> rgs [mem_config_def]) >>
    drule evaluate_ext_call >>
    disch_then (qspecl_then [‘MAP explode (out_signals prog)’,‘bytes’] mp_tac) >>
    rgs [] >>
    impl_tac
    >- (
      unabbrev_all_tac >> rgs [ffi_vars_def, FLOOKUP_UPDATE]) >>
    strip_tac >> rveq >> rgs [] >>
    pop_assum kall_tac >>
    unabbrev_all_tac >> rgs [] >>
    (* reading systime *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «sysTime» _, nt)’ >>
    ‘nt.memory nt.base_addr = Word (n2w (FST(t.ffi.ffi_state 0)))’ by (
      fs [Abbr ‘nt’] >>
      rgs [mem_call_ffi_def] >>
      qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
      rgs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, nt) = (_, ft)’ >>
      first_x_assum (qspecl_then [‘nt’, ‘ft’] mp_tac) >>
      impl_tac
      >- (
        rgs [Abbr ‘ft’, Abbr ‘nt’, nexts_ffi_def, ETA_AX] >> metis_tac []) >>
      strip_tac >>
      rgs [Abbr ‘ft’, nexts_ffi_def, init_ffi_def]) >>
    drule evaluate_assign_load >>
    rgs [] >>
    disch_then (qspecl_then
                [‘t.base_addr’, ‘0w’,
                 ‘n2w (FST (t.ffi.ffi_state 0))’] mp_tac) >>
    impl_tac
    >- (unabbrev_all_tac >> rgs [FLOOKUP_UPDATE, mem_config_def]) >>
    strip_tac >> unabbrev_all_tac >> rveq >> rgs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    (* reading input to the variable event *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    qmatch_asmsub_abbrev_tac ‘evaluate (Assign «event» _, nnt)’ >>
    ‘nnt.memory (t.base_addr +  bytes_in_word) =
     Word (n2w (SND(t.ffi.ffi_state 0)))’ by (
      fs [Abbr ‘nnt’] >>
      qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
      rgs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, nt) = (_, ft)’ >>
      last_x_assum (qspecl_then [‘nt’, ‘ft’] mp_tac) >>
      impl_tac
      >- (gs [Abbr ‘ft’, Abbr ‘nt’, nexts_ffi_def, ETA_AX] >> metis_tac []) >>
      strip_tac >>
      rgs [Abbr ‘ft’, nexts_ffi_def, init_ffi_def]) >>
    rgs [] >>
    drule evaluate_assign_load_next_address >>
    rgs [] >>
    disch_then (qspecl_then
                [‘t.base_addr’,
                 ‘n2w (SND (t.ffi.ffi_state 0))’] mp_tac) >>
    impl_tac
    >- (unabbrev_all_tac >> rgs [FLOOKUP_UPDATE, mem_config_def]) >>
    strip_tac >>
    unabbrev_all_tac >>
    rgs [] >> rveq >> rgs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    (* isInput *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    drule evaluate_assign_compare_next_address >>
    rgs [] >>
    disch_then (qspecl_then [‘t.base_addr’] mp_tac) >>
    impl_tac
    >- (
      rgs [FLOOKUP_UPDATE, mem_call_ffi_def] >>
      qpat_x_assum ‘mem_read_ffi_results _ _ _’ assume_tac >>
      rgs [mem_read_ffi_results_def] >>
      qmatch_asmsub_abbrev_tac ‘evaluate (ExtCall _ _ _ _ _, nt) = (_, ft)’ >>
      first_x_assum (qspecl_then [‘nt’, ‘ft’] mp_tac) >>
      impl_tac
      >- (
        rgs [Abbr ‘ft’, Abbr ‘nt’, nexts_ffi_def, ETA_AX] >> metis_tac []) >>
      strip_tac >>
      rgs [Abbr ‘ft’, nexts_ffi_def, init_ffi_def, mem_config_def]) >>
    strip_tac >> rveq >> rgs [] >>
    pop_assum kall_tac >>
    (* If statement *)
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> fs [] >>
    drule evaluate_if_compare_sys_time >>
    disch_then (qspec_then ‘FST (t.ffi.ffi_state 0)’ mp_tac) >>
    impl_tac
    >- (
      unabbrev_all_tac >>
      rgs [FLOOKUP_UPDATE]) >>
    strip_tac >> rveq >> rgs [] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    strip_tac >> fs [] >>
    rveq >> rgs [] >>
    pairarg_tac >> rveq >> rgs [] >>
    rgs [eval_def, FLOOKUP_UPDATE] >>
    qmatch_asmsub_abbrev_tac ‘eval nt _’ >>
    ‘FLOOKUP nt.locals «sysTime» = SOME (ValWord (n2w (FST (t.ffi.ffi_state 0))))’ by
      rgs [Abbr ‘nt’,FLOOKUP_UPDATE] >>
    drule eval_mkClks >>
    disch_then (qspec_then ‘nClks prog’ assume_tac) >>
    fs [] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    fs [is_valid_value_def, FLOOKUP_UPDATE] >>
    fs [panSemTheory.shape_of_def] >>
    rgs [replicate_shape_one] >>
    unabbrev_all_tac >> rveq >> rgs[] >>
    pop_assum kall_tac >>
    pop_assum kall_tac >>
    pairarg_tac >> rveq >> rgs [] >>
    pop_assum mp_tac >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    qmatch_goalsub_abbrev_tac ‘eval tt q’ >>
    ‘eval tt q =
     SOME (ValWord (n2w (
                     case st.waitTime of
                     | NONE => FST (t.ffi.ffi_state 0)
                     | SOME n => FST (t.ffi.ffi_state 0) + n)))’ by (
      cases_on ‘st.waitTime’ >>
      unabbrev_all_tac >>
      rgs [eval_def, FLOOKUP_UPDATE, OPT_MMAP_def,
          wordLangTheory.word_op_def, word_add_n2w]) >>
    rgs [is_valid_value_def, FLOOKUP_UPDATE, shape_of_def] >>
    strip_tac >> rveq >> rgs [] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    pairarg_tac >> rveq >> rgs [] >>
    rewrite_tac [Once evaluate_def] >>
    fs [] >>
    (* until always *)
    rgs [locals_before_start_ctrl_def] >>
    strip_tac >>
    gvs [empty_locals_def] >>
    rgs [ffi_call_ffi_def] >>
    gvs [shape_of_def, set_var_def] >>
    strip_tac >> gvs [] >>
    strip_tac >> gvs [panLangTheory.size_of_shape_def] >>
    qexists_tac ‘ns’ >> gvs []) >>
  rgs [semantics_def] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  rw []
  >- (
    cases_on
    ‘evaluate (TailCall (Label «start» ) [],t with clock := k')’ >>
    rgs [] >>
    cases_on ‘q = SOME TimeOut’ >>
    rgs [] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    drule evaluate_add_clock_eq >>
    rgs [] >>
    disch_then (qspec_then ‘k'’ assume_tac) >>
    rgs [] >>
    strip_tac >>
    strip_tac >>
    strip_tac >>
    strip_tac >>
    drule evaluate_add_clock_eq >>
    rgs [] >>
    disch_then (qspec_then ‘ck + t.clock’ assume_tac) >>
    rgs [])
  >- (
    rgs [] >>
    first_x_assum (qspec_then ‘ck + t.clock’ assume_tac) >> rgs [] >>
    cases_on ‘r = SOME TimeOut’ >>
    rgs [] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    drule evaluate_add_clock_eq >>
    rgs [] >>
    disch_then (qspec_then ‘k’ assume_tac) >>
    rgs [] >>
    strip_tac >>
    strip_tac >>
    strip_tac >>
    drule evaluate_add_clock_eq >>
    rgs [] >>
    disch_then (qspec_then ‘ck + t.clock’ assume_tac) >>
    rgs [] >> gvs [] >>
    MAP_EVERY qexists_tac [‘io’, ‘ios’, ‘ns’] >>
    gvs [state_component_equality])
  >- (
    cases_on
    ‘evaluate (TailCall (Label «start» ) [],t with clock := k)’ >>
    rgs [] >>
    cases_on ‘q = SOME TimeOut’ >>
    rgs [] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    drule evaluate_add_clock_eq >>
    rgs [] >>
    disch_then (qspec_then ‘k’ assume_tac) >>
    rgs [] >>
    strip_tac >>
    strip_tac >>
    drule evaluate_add_clock_eq >>
    rgs [] >>
    disch_then (qspec_then ‘ck + t.clock’ assume_tac) >>
    rgs []) >>
  rgs [] >>
  qexists_tac ‘ck + t.clock’ >>
  rgs []
QED

Theorem timed_automata_until_panic_functional_correct:
  ∀k prog or st sts labels (t:('a,time_input) panSem$state).
    timeFunSem$eval_steps k prog
               (dimword (:α) - 1) (FST (t.ffi.ffi_state 0))
               or st = SOME (labels, sts) ∧
    has_panic labels ∧ byte_align t.base_addr = t.base_addr ∧
    wf_prog_and_init_states prog st t ∧
    ffi_rels_after_init prog (uptil_panic labels) st t ∧
    sum_delays_until_panic (:α) (until_panic labels) (next_ffi t.ffi.ffi_state) ⇒
    ∃io ios ns.
      semantics t «start» = Terminate Success (io::ios) ∧
      LENGTH (slice_labels labels) = LENGTH ns ∧
      SUM ns = LENGTH ios ∧
      decode_ios (:α) t.be (slice_labels labels) ns (io::ios)
Proof
  rw [] >>
  dxrule eval_steps_imp_steps >>
  strip_tac >>
  metis_tac [timed_automata_until_panic_correct]
QED


Theorem io_trace_impl_eval_steps_uptil_panic:
  ∀prog st (t:('a,time_input) panSem$state) or k.
    wf_prog_init_states prog or k st t ∧
    ffi_rels_after_init prog
                        (uptil_panic (labels_of k prog (dimword (:α) - 1) (systime_at t) or st))
                        st t ∧
    has_panic (labels_of k prog (dimword (:α) - 1) (systime_at t) or st) ∧
    byte_align t.base_addr = t.base_addr ∧
    sum_delays_until_panic (:α)
                           (until_panic (labels_of k prog (dimword (:α) - 1) (systime_at t) or st))
                           (next_ffi t.ffi.ffi_state) ⇒
    ∃lbls sts io ios ns.
      timeFunSem$eval_steps k prog (dimword (:α) - 1) (systime_at t) or st =
      SOME (lbls, sts) ∧
      semantics t «start» = Terminate Success (io::ios) ∧
      LENGTH (slice_labels lbls) = LENGTH ns ∧
      SUM ns = LENGTH ios ∧
      decode_ios (:α) t.be (slice_labels lbls) ns (io::ios)
Proof
  rw [] >>
  rgs [wf_prog_init_states_def, systime_at_def] >>
  ‘∃lbls sts.
     timeFunSem$eval_steps k prog (dimword (:α) − 1)
                           (FST (t.ffi.ffi_state 0)) or st = SOME (lbls,sts)’ by (
    rgs [GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >>
    cases_on ‘(timeFunSem$eval_steps k prog (dimword (:α) − 1)
               (FST (t.ffi.ffi_state 0)) or st)’ >>
    rgs [IS_SOME_DEF] >>
    cases_on ‘x’ >> rgs []) >>
  rgs [labels_of_def] >>
  metis_tac [timed_automata_until_panic_functional_correct,
             wf_prog_and_init_states_def]
QED

Definition labels_and_ffi_assumptions_def:
  labels_and_ffi_assumptions (:α) prog lbls st t ⇔
    (no_panic lbls ∧ byte_align t.base_addr = t.base_addr ∧
     sum_delays (:α) lbls (next_ffi t.ffi.ffi_state) ∧
     ffi_rels_after_init prog lbls st t) ∨
    (has_panic lbls ∧ byte_align t.base_addr = t.base_addr ∧
     ffi_rels_after_init prog (uptil_panic lbls) st t ∧
     sum_delays_until_panic (:α) (until_panic lbls) (next_ffi t.ffi.ffi_state))
End

Theorem no_panic_imp_not_has_panic:
  ∀lbls.
    no_panic lbls ⇒ ~has_panic lbls
Proof
  Induct >>
  rw [no_panic_def, has_panic_def] >>
  metis_tac []
QED

Theorem has_panic_imp_not_no_panic:
  ∀lbls.
    has_panic lbls ⇒ ~no_panic lbls
Proof
  Induct >>
  rw [no_panic_def, has_panic_def] >>
  metis_tac [timed_automata_until_panic_functional_correct]
QED


Theorem steps_impl_io_trace:
  ∀k prog or st sts labels (t:('a,time_input) panSem$state).
    timeFunSem$eval_steps k prog
                          (dimword (:α) - 1) (FST (t.ffi.ffi_state 0))
                          or st = SOME (labels, sts) ∧
    labels_and_ffi_assumptions (:α) prog labels st t ∧
    wf_prog_and_init_states prog st t ⇒
    ∃io ios ns.
      semantics t «start» = Terminate Success (io::ios) ∧
      (no_panic labels ⇒
       LENGTH labels = LENGTH ns ∧
       SUM ns + 1 = LENGTH ios ∧
       decode_ios (:α) t.be labels ns (io::FRONT ios)) ∧
      (has_panic labels ⇒
       LENGTH (slice_labels labels) = LENGTH ns ∧
       SUM ns = LENGTH ios ∧
       decode_ios (:α) t.be (slice_labels labels) ns (io::ios))
Proof
  rw [] >>
  rgs [labels_and_ffi_assumptions_def,
      no_panic_imp_not_has_panic, has_panic_imp_not_no_panic] >>
  metis_tac [timed_automata_no_panic_functional_correct,
             timed_automata_until_panic_functional_correct]
QED

Definition io_events_and_ffi_assumptions_def:
  io_events_and_ffi_assumptions (:α) k prog or st t ⇔
    (ffi_rels_after_init prog
     (labels_of k prog (dimword (:α) - 1) (systime_at t) or st) st t ∧
     no_panic (labels_of k prog (dimword (:α) - 1) (systime_at t) or st) ∧
     byte_align t.base_addr = t.base_addr ∧
     sum_delays (:α) (labels_of k prog (dimword (:α) - 1) (systime_at t) or st)
                (next_ffi t.ffi.ffi_state)) ∨
    (ffi_rels_after_init prog
     (uptil_panic (labels_of k prog (dimword (:α) - 1) (systime_at t) or st))
     st t ∧
     has_panic (labels_of k prog (dimword (:α) - 1) (systime_at t) or st) ∧
     byte_align t.base_addr = t.base_addr ∧
     sum_delays_until_panic (:α)
                            (until_panic (labels_of k prog (dimword (:α) - 1) (systime_at t) or st))
                            (next_ffi t.ffi.ffi_state))
End


Theorem io_trace_impl_steps:
  ∀prog st (t:('a,time_input) panSem$state) or k.
    wf_prog_init_states prog or k st t ∧
    io_events_and_ffi_assumptions (:α) k prog or st t ⇒
    ∃lbls sts io ios ns.
      timeFunSem$eval_steps k prog (dimword (:α) - 1) (systime_at t) or st =
      SOME (lbls, sts) ∧
      semantics t «start» = Terminate Success (io::ios) ∧
      (no_panic (labels_of k prog (dimword (:α) - 1) (systime_at t) or st) ⇒
       LENGTH lbls = LENGTH ns ∧ SUM ns + 1 = LENGTH ios ∧
       decode_ios (:α) t.be lbls ns (io::FRONT ios)) ∧
      (has_panic (labels_of k prog (dimword (:α) - 1) (systime_at t) or st) ⇒
       LENGTH (slice_labels lbls) = LENGTH ns ∧
       SUM ns = LENGTH ios ∧
       decode_ios (:α) t.be (slice_labels lbls) ns (io::ios))
Proof
  rw [] >>
  rgs [io_events_and_ffi_assumptions_def,
      no_panic_imp_not_has_panic, has_panic_imp_not_no_panic] >>
  metis_tac [io_trace_impl_eval_steps,
             io_trace_impl_eval_steps_uptil_panic]
QED

(*
Definition ndecode_ios_def:
  (ndecode_ios (:α) _ [] _ ios ⇔ LENGTH ios = 0) ∧
  (ndecode_ios (:α) be (lbl::lbls) e (io::ios) ⇔
   case lbl of
   | LDelay d =>
       (if d = 0 then
        ndecode_ios (:α) be lbls e (io::ios)
        else
          let
            m' = EL 0 (io_event_dest (:α) be e);
            obs_ios = decode_io_events (:'a) be io;
            m = THE (to_delay (EL (LENGTH obs_ios - 1) obs_ios))
          in
            d = m - m' ∧
            ndecode_ios (:α) be lbls (LAST io) ios)
   | LAction act =>
        (ndecode_ios (:α) be lbls (LAST io) ios ∧
         (case act of
          | Input i =>
              let
                obs_io = decode_io_event (:α) be (EL 0 io)
              in
                Input i = THE (to_input obs_io)
          | Output os =>
              decode_io_event (:α) be (EL 0 io) = ObsOutput os))
    | LPanic p =>
        case p of
        | PanicInput i =>
            let
              obs_io = decode_io_event (:α) be (EL 0 io)
            in
              Input i = THE (to_input obs_io)
        | _ => F) ∧
  (ndecode_ios (:α) _ _ _ _ ⇔ F)
End
*)

val _ = export_theory();
