(*
  Shared command-line parsing and output helpers for the compilers.
*)
Theory compiler_common
Ancestors
  lexer_impl backend mlstring location
  x64_config export_x64 arm8_config export_arm8
  riscv_config export_riscv mips_config export_mips
  arm7_config export_arm7 ag32_config export_ag32
Libs
  preamble

Definition print_option_def:
  print_option h x =
    case x of
      NONE => «»
    | SOME y => h ^ « » ^ y ^ «\n»
End

Definition find_next_newline_def:
  find_next_newline n s =
    if strlen s ≤ n then n else
      if strsub s n = #"\n" then n else
        find_next_newline (n+1) s
Termination
  WF_REL_TAC ‘measure (λ(n,s). strlen s - n)’
End

Definition safe_substring_def:
  safe_substring s n l =
    let k = strlen s in
      if k ≤ n then «» else
        if n + l ≤ k then
          substring s n l
        else substring s n (k - n)
End

Definition get_nth_line_def:
  get_nth_line k s n =
    if k = 0 then
      let n1 = find_next_newline n s in
        safe_substring s n (n1 - n)
    else
      get_nth_line (k-1:num) s (find_next_newline n s + 1)
End

Definition locs_to_string_def:
  (locs_to_string input NONE = implode "unknown location") ∧
  (locs_to_string input (SOME (location$Locs startl endl)) =
    case startl of
    | POSN r c =>
       (let line = get_nth_line r input 0 in
        let len = strlen line in
        let stop =
          (case endl of POSN r1 c1 => (if r1 = r then c1 else len) | _ => len) in
        let underline =
          concat (REPLICATE c « » ++ REPLICATE ((stop - c) + 1) (strlit [CHR 94])) in
          concat [«line »; toString (r+1); «\n\n»;
                  line; «\n»;
                  underline;  «\n»])
    | _ => implode "unknown location")
End

Definition is_error_msg_def:
  is_error_msg x = mlstring$isPrefix «###» x
End

Definition parse_num_def:
  parse_num str =
  let str = explode str in
  if EVERY isDigit str
  then
    SOME (num_from_dec_string_alt str)
  else NONE
End

Definition parse_bool_def:
  parse_bool str =
  if str = «true» then SOME T
  else if str = «false» then SOME F
  else NONE
End

Definition find_str_def:
  (find_str flag [] = NONE) ∧
  (find_str flag (x::xs) =
    if isPrefix flag x then
      SOME (extract x (strlen flag) NONE)
    else
      find_str flag xs)
End

Definition find_strs_def:
  (find_strs flag [] = []) /\
  (find_strs flag (x::xs) =
    if isPrefix flag x then
      (extract x (strlen flag) NONE) :: find_strs flag xs
    else
      find_strs flag xs)
End

Definition find_bool_def:
  find_bool flag ls default =
  case find_str flag ls of
    NONE => INL default
  | SOME rest =>
    case parse_bool rest of
      SOME b => INL b
    | NONE => INR (concat [«Unable to parse as bool: »;rest;« for flag: »;flag])
End

Definition find_num_def:
  find_num flag ls default =
  case find_str flag ls of
    NONE => INL default
  | SOME rest =>
  case parse_num rest of
    SOME n => INL n
  | NONE => INR (concat [«Unable to parse as num: »;rest;« for flag: »;flag])
End

Definition get_err_str_def:
  (get_err_str (INL n) = «») ∧
  (get_err_str (INR n) = concat[n;«\n»])
End

Definition parse_num_list_def:
  (parse_num_list [] = INL []) /\
  (parse_num_list (x::xs) =
     case parse_num x of
       NONE => INR (concat [«Unable to parse as num: »;x])
     | SOME n =>
       case parse_num_list xs of
         INR s => INR s
       | INL ns => INL (n::ns))
End

Definition comma_tokens_def:
  (comma_tokens acc xs [] = if NULL xs then acc else acc ++ [implode xs]) /\
  (comma_tokens acc (xs:string) (c::(cs:string)) =
    if c = #"," then
      comma_tokens (acc ++ if NULL xs then [] else [implode xs]) [] cs
    else
      comma_tokens acc (STRCAT xs [c]) cs)
End

Definition parse_nums_def:
  parse_nums str = (parse_num_list (comma_tokens [] [] (explode str)))
End

Definition parse_clos_conf_def:
  parse_clos_conf ls clos =
  let multi = find_bool «--multi=» ls clos.do_mti in
  let known = find_bool «--known=» ls (IS_SOME clos.known_conf) in
  let inline_factor = find_num «--inline_factor=» ls default_inline_factor in
  let call = find_bool «--call=» ls clos.do_call in
  let maxapp =
    (case find_num «--max_app=» ls clos.max_app of
     | INL n => if 0 < n ∧ n ≤ max_app_limit then INL n
                else INR «--max_app must be between 1 and 1000»
     | err => err) in
  case (multi,known,inline_factor,call,maxapp) of
    (INL m,INL k,INL i,INL c,INL n) =>
    if k then
    (let max_body_size = find_num «--max_body_size=» ls (default_max_body_size n i) in
     case max_body_size of
      (INL x) =>
      INL
        (clos with <|
          do_mti   := m;
          known_conf := SOME (clos_known$mk_config x i);
          do_call  := c;
          max_app  := n
         |>)
      | _ => INR (concat [get_err_str max_body_size]))
    else
    (INL
      (clos with <|
        do_mti   := m;
        known_conf := NONE;
        do_call  := c;
        max_app  := n
       |>))
  | _ =>
    INR (concat [get_err_str multi;
                 get_err_str known;
                 get_err_str inline_factor;
                 get_err_str call;
                 get_err_str maxapp])
End

Definition parse_bvl_conf_def:
  parse_bvl_conf ls bvl =
  let inlinesz = find_num «--inline_size=» ls bvl.inline_size_limit in
  let expcut = find_num «--exp_cut=» ls bvl.exp_cut in
  let tmc = find_bool «--tmc=» ls bvl.do_tmc in
  let tailrec = find_bool «--tailrec=» ls bvl.do_tailrec in
  let splitmain = find_bool «--split=» ls bvl.split_main_at_seq in
  case (inlinesz,expcut,splitmain,tmc,tailrec) of
    (INL i,INL e,INL m,INL do_tmc,INL do_tailrec) =>
    INL
      (bvl with <|
        inline_size_limit := i;
        exp_cut           := e;
        split_main_at_seq := m;
        do_tmc            := do_tmc;
        do_tailrec        := do_tailrec;
      |>)
  | _ =>
    INR (concat [get_err_str inlinesz;
                 get_err_str expcut;
                 get_err_str splitmain;
                 get_err_str tmc;
                 get_err_str tailrec])
End

Definition parse_wtw_conf_def:
  parse_wtw_conf ls wtw =
    let regalg = find_num «--reg_alg=» ls wtw.reg_alg in
      case regalg of
        INL r => INL (wtw with <|reg_alg:= r |>)
      | INR s => INR (get_err_str regalg)
End

Definition parse_gc_def:
  parse_gc ls default =
  case find_str «--gc=» ls of
    NONE => INL default
  | SOME rest =>
    if rest = «none» then INL None
    else if rest = «simple» then INL Simple
    else if isPrefix «gen» rest then
      case parse_nums (extract rest (strlen «gen») NONE) of
        INL ls => INL (Generational ls)
      | INR s =>
        INR (concat [«Error parsing GenGC argument: »;s])
    else INR (concat [«Unrecognized GC option: »;rest])
End

Definition conf_ok_check_def:
  conf_ok_check (:'a) c <=>
    arch_width_bits c.arch_width = dimindex (:α) ∧
    shift_length c < dimindex (:α) ∧
    backend_common$word_shift (dimindex (:α)) ≤ shift_length c ∧ c.len_size ≠ 0 ∧
    c.len_size + 9 < dimindex (:α)
End

Definition parse_data_conf_def:
  parse_data_conf ls data =
  let tag_bits = find_num «--tag_bits=» ls data.tag_bits in
  let len_bits = find_num «--len_bits=» ls data.len_bits in
  let pad_bits = find_num «--pad_bits=» ls data.pad_bits in
  let len_size = find_num «--len_size=» ls data.len_size in
  let empty_FFI= find_bool «--emit_empty_ffi=» ls data.call_empty_ffi in
  let gc = parse_gc ls data.gc_kind in
  case (tag_bits,len_bits,pad_bits,len_size,gc,empty_FFI) of
    (INL tb,INL lb,INL pb,INL ls,INL gc, INL empty_FFI) =>
      (* TODO: check conf_ok here and raise error if violated *)
      INL (data with
      <| tag_bits := tb;
         len_bits := lb;
         pad_bits := pb;
         len_size := ls;
         gc_kind  := gc;
         call_empty_ffi := empty_FFI |>)
  | _ =>
     INR (concat [get_err_str tag_bits;
                  get_err_str len_bits;
                  get_err_str pad_bits;
                  get_err_str len_size;
                  get_err_str gc;
                  get_err_str empty_FFI])
End

Definition parse_stack_conf_def:
  parse_stack_conf ls stack =
  let jump = find_bool «--jump=» ls stack.jump in
  let perf = find_bool «--perf_callgraph=» ls stack.perf_calls in
  case (jump, perf) of
    (INL j, INL p) => INL (stack with <| jump := j; perf_calls := p |>)
  | (INR s, _) => INR s
  | (_, INR s) => INR s
End

Definition parse_tap_conf_def:
  parse_tap_conf ls stack =
    INL (<| explore_flag := MEM «--explore» ls |>)
End

Definition parse_lab_conf_def:
  parse_lab_conf ls lab =
    let hs = find_num «--hash_size=» ls lab.hash_size in
      case hs of
        INL r => INL (lab with <|hash_size := r |>)
      | INR s => INR s
End

Definition extend_conf_def:
  extend_conf ls conf =
  let clos = parse_clos_conf ls conf.clos_conf in
  let bvl = parse_bvl_conf ls conf.bvl_conf in
  let wtw = parse_wtw_conf ls conf.word_to_word_conf in
  let data = parse_data_conf ls conf.data_conf in
  let stack = parse_stack_conf ls conf.stack_conf in
  let tap = parse_tap_conf ls conf.tap_conf in
  let lab = parse_lab_conf ls conf.lab_conf in
  case (clos,bvl,wtw,data,stack,tap,lab) of
    (INL clos,INL bvl,INL wtw,INL data,INL stack,INL tap, INL lab) =>
      INL (conf with
        <|clos_conf         := clos;
          bvl_conf          := bvl;
          word_to_word_conf := wtw;
          data_conf         := data;
          stack_conf        := stack;
          tap_conf          := tap;
          lab_conf          := lab|>)
    | _ =>
      INR (concat [get_err_str clos;
               get_err_str bvl;
               get_err_str wtw;
               get_err_str data;
               get_err_str stack;
               get_err_str tap;
               get_err_str lab])
End

Definition parse_target_def:
  parse_target ls =
  case find_str «--target=» ls of
    NONE => INL (x64_backend_config,x64_export,x64_config)
  | SOME rest =>
    if rest = «x64» then INL (x64_backend_config,x64_export,x64_config)
    else if rest = «arm8» then INL (arm8_backend_config,arm8_export,arm8_config)
    else if rest = «mips» then INL (mips_backend_config,mips_export,mips_config)
    else if rest = «riscv» then INL (riscv_backend_config,riscv_export,riscv_config)
    else if rest = «arm7» then INL (arm7_backend_config,arm7_export,arm7_config)
    else if rest = «ag32» then INL (ag32_backend_config,ag32_export,ag32_config)
    else INR (concat [«Unrecognized target option: »;rest])
End

Definition has_version_flag_def:
  has_version_flag ls = MEM «--version» ls
End

Definition has_help_flag_def:
  has_help_flag ls = MEM «--help» ls
End

Definition add_tap_output_def:
  add_tap_output td out =
    if td = Nil then out else td :mlstring app_list
End
