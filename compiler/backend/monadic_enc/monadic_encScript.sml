(*
  Implement and prove correct monadic version of encoder
*)
open preamble state_transformerTheory
open ml_monadBaseLib ml_monadBaseTheory
open asmTheory lab_to_targetTheory

val _ = new_theory "monadic_enc"
val _ = ParseExtras.temp_tight_equality();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

(* The state is just an array *)
val _ = Hol_datatype `
  enc_state_64 = <|
       hash_tab : ((64 asm # word8 list) list) list
     |>`

val accessors = define_monad_access_funs ``:enc_state_64``;

val hash_tab_accessors = el 1 accessors;
val (hash_tab,get_hash_tab_def,set_hash_tab_def) = hash_tab_accessors;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | Subscript`;

(* Monadic functions to handle the exceptions *)
val exn_functions = define_monad_exception_functions ``:state_exn`` ``:enc_state_64``;
val _ = temp_overload_on ("failwith", ``raise_Fail``);

val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;

(* Fixed-size array manipulators *)
val arr_manip = define_MFarray_manip_funs
  [hash_tab_accessors] sub_exn update_exn;

fun accessor_thm (a,b,c,d,e,f) = LIST_CONJ [b,c,d,e,f]

val hash_tab_manip = el 1 arr_manip;

val hash_tab_accessor = save_thm("hash_tab_accessor",accessor_thm hash_tab_manip);

(* There are probably better ways to hash *)

val hash_reg_imm_def = Define`
  (hash_reg_imm (Reg reg) = reg) ∧
  (hash_reg_imm (Imm imm) = 64n + w2n imm)`

val hash_binop_def = Define`
  (hash_binop Add = 2n) ∧
  (hash_binop Sub = 3n) ∧
  (hash_binop And = 5n) ∧
  (hash_binop Or  = 7n) ∧
  (hash_binop Xor = 11n)`

val hash_cmp_def = Define`
  (hash_cmp Equal = 2n) ∧
  (hash_cmp Lower = 3n) ∧
  (hash_cmp Less  = 5n) ∧
  (hash_cmp Test  = 7n) ∧
  (hash_cmp NotEqual = 11n) ∧
  (hash_cmp NotLower = 13n) ∧
  (hash_cmp NotLess  = 17n) ∧
  (hash_cmp NotTest  = 19n)`

val hash_shift_def = Define`
  (hash_shift Lsl = 2n) ∧
  (hash_shift Lsr = 3n) ∧
  (hash_shift Asr = 5n) ∧
  (hash_shift Ror = 7n)`

val hash_arith_def = Define`
  (hash_arith (Binop bop r1 r2 ri) =
    2n * (2n * (2n * hash_binop bop + r1) + r2) + hash_reg_imm ri) ∧
  (hash_arith (Shift sh r1 r2 n) =
    3n * (3n * (3n * hash_shift sh + r1) + r2) + n) ∧
  (hash_arith (Div r1 r2 r3) = (5n * (5n * r1 + r2) + r3)) ∧
  (hash_arith (LongMul r1 r2 r3 r4) = 7n * (7n * (7n * r1 + r2) + r3) + r4) ∧
  (hash_arith (LongDiv r1 r2 r3 r4 r5) =
    11n * (11n * (11n * (11n * r1 + r2) + r3) + r4) + r5) ∧
  (hash_arith (AddCarry r1 r2 r3 r4) = 13n * (13n * (13n * r1 + r2) + r3) + r4) ∧
  (hash_arith (AddOverflow r1 r2 r3 r4) = 17n * (17n * (17n * r1 + r2) + r3) + r4) ∧
  (hash_arith (SubOverflow r1 r2 r3 r4) = 19n * (19n * (19n * r1 + r2) + r3) + r4)`

val hash_memop_def = Define`
  (hash_memop Load   = 2n) ∧
  (hash_memop Load8  = 3n) ∧
  (hash_memop Store  = 5n) ∧
  (hash_memop Store8 = 7n)`

val hash_fp_def = Define`
  (hash_fp (FPLess r f1 f2) = 2n * (2n * r + f1) + f2) ∧
  (hash_fp (FPLessEqual r f1 f2) = 3n * (3n * r + f1) + f2) ∧
  (hash_fp (FPEqual r f1 f2) = 5n * (5n * r + f1) + f2) ∧

  (hash_fp (FPAbs f1 f2) = 7n * f1 + f2) ∧
  (hash_fp (FPNeg f1 f2) = 11n * f1 + f2) ∧
  (hash_fp (FPSqrt f1 f2) = 13n * f1 + f2) ∧

  (hash_fp (FPAdd f1 f2 f3) = 17n * (17n * f1 + f2) + f3) ∧
  (hash_fp (FPSub f1 f2 f3) = 19n * (19n * f1 + f2) + f3) ∧
  (hash_fp (FPMul f1 f2 f3) = 23n * (23n * f1 + f2) + f3) ∧
  (hash_fp (FPDiv f1 f2 f3) = 29n * (29n * f1 + f2) + f3) ∧

  (hash_fp (FPMov f1 f2) = 31n * f1 + f2) ∧
  (hash_fp (FPMovToReg r1 r2 f) = 37n * (37n * r1 + r2) + f) ∧
  (hash_fp (FPMovFromReg f r1 r2) = 41n * (41n * f + r1) + r2) ∧
  (hash_fp (FPToInt f1 f2) = 43n * f1 + f2) ∧
  (hash_fp (FPFromInt f1 f2) = 47n * f1 + f2)`

val hash_inst_def = Define`
  (hash_inst Skip = 2n) ∧
  (hash_inst (Const r w) = (3n * r + w2n w)) ∧
  (hash_inst (Arith a) = (5n * hash_arith a)) ∧
  (hash_inst (Mem m r (Addr rr w)) =
    7n * (7n * (7n * hash_memop m + r) + rr) + w2n w) ∧
  (hash_inst (FP fp) =
    9n * hash_fp fp)`

val hash_asm_def = Define`
  (hash_asm (Inst i) = 2n * hash_inst i) ∧
  (hash_asm (Jump w) = 3n * w2n w) ∧
  (hash_asm (JumpCmp c r ri w) = 5n * (5n * (5n * (hash_cmp c) + r) + hash_reg_imm ri) + w2n w) ∧
  (hash_asm (Call w) = 7n * w2n w) ∧
  (hash_asm (JumpReg r) = 9n * r) ∧
  (hash_asm (Loc r w) = 11n * r + w2n w)`

val lookup_insert_table_def = Define`
  lookup_insert_table enc n a =
  let v = hash_asm a MOD n in
  do
    ls <- hash_tab_sub v;
    case ALOOKUP ls a of
      NONE =>
      do
        encode <- return (enc a);
        update_hash_tab v ((a,encode)::ls);
        return encode
      od
    | SOME res =>
      return res
  od`

val enc_line_hash_def = Define `
  (enc_line_hash enc skip_len n (Label n1 n2 n3) =
    return (Label n1 n2 skip_len)) ∧
  (enc_line_hash enc skip_len n (Asm a _ _) =
    do
      bs <- lookup_insert_table enc n (cbw_to_asm a);
      return (Asm a bs (LENGTH bs))
    od) ∧
  (enc_line_hash enc skip_len n (LabAsm l _ _ _) =
     do
       bs <- lookup_insert_table enc n (lab_inst 0w l);
       return (LabAsm l 0w bs (LENGTH bs))
     od)`

val enc_line_hash_ls_def = Define`
  (enc_line_hash_ls enc skip_len n [] = return []) ∧
  (enc_line_hash_ls enc skip_len n (x::xs) =
  do
    fx <- enc_line_hash enc skip_len n x;
    fxs <- enc_line_hash_ls enc skip_len n xs;
    return (fx::fxs)
  od)`

val enc_sec_hash_ls_def = Define`
  (enc_sec_hash_ls enc skip_len n [] = return []) ∧
  (enc_sec_hash_ls enc skip_len n (x::xs) =
  case x of Section k ys =>
  do
    ls <- enc_line_hash_ls enc skip_len n ys;
    rest <- enc_sec_hash_ls enc skip_len n xs;
    return (Section k ls::rest)
  od)`

val enc_sec_hash_ls_full_def = Define`
  enc_sec_hash_ls_full enc n xs =
  enc_sec_hash_ls enc (LENGTH (enc (Inst Skip))) n xs`

(* As we are using fixed-size array, we need to define a different record type for the initialization *)
val array_fields_names = ["hash_tab"];
val run_ienc_state_64_def = define_run ``:enc_state_64``
                                      array_fields_names
                                      "ienc_state_64";

val enc_secs_aux_def = Define`
  enc_secs_aux enc n xs =
    run_ienc_state_64 (enc_sec_hash_ls_full enc n xs) <| hash_tab := (n, []) |>`

val enc_secs_def = Define`
  enc_secs enc n xs =
    case enc_secs_aux enc (if n = 0 then 1 else n) xs of
      Success xs => xs
    | Failure _ => []`

(* prove that enc_secs gives the same behavior as enc_sec_list *)

val msimps = [st_ex_bind_def,st_ex_return_def];

Theorem Msub_eqn[simp] `
  ∀e n ls v.
  Msub e n ls =
  if n < LENGTH ls then Success (EL n ls)
                   else Failure e`
  (ho_match_mp_tac Msub_ind>>rw[]>>
  simp[Once Msub_def]>>
  Cases_on`ls`>>fs[]>>
  IF_CASES_TAC>>fs[]>>
  Cases_on`n`>>fs[]);

Theorem hash_tab_sub_eqn[simp] `
  hash_tab_sub n s =
  if n < LENGTH s.hash_tab then
    (Success (EL n s.hash_tab),s)
  else
    (Failure (Subscript),s)`
  (rw[fetch "-" "hash_tab_sub_def"]>>
  fs[Marray_sub_def]);

Theorem Mupdate_eqn[simp] `
  ∀e x n ls.
  Mupdate e x n ls =
  if n < LENGTH ls then
    Success (LUPDATE x n ls)
  else
    Failure e`
  (ho_match_mp_tac Mupdate_ind>>rw[]>>
  simp[Once Mupdate_def]>>
  Cases_on`ls`>>fs[]>>
  IF_CASES_TAC>>fs[LUPDATE_def]>>
  Cases_on`n`>>fs[LUPDATE_def]);

Theorem update_hash_tab_eqn[simp] `
  update_hash_tab n t s =
  if n < LENGTH s.hash_tab then
     (Success (),s with hash_tab := LUPDATE t n s.hash_tab)
  else
     (Failure (Subscript),s)`
  (rw[fetch "-" "update_hash_tab_def"]>>
  fs[Marray_update_def]);

val good_table_def = Define`
  good_table enc n s ⇔
  EVERY (λls. EVERY (λ(x,y). enc x = y) ls) s.hash_tab ∧
  LENGTH s.hash_tab = n`

val lookup_insert_table_correct = Q.prove(`
  good_table enc n s ∧
  0 < n ⇒
  ∃s'.
  lookup_insert_table enc n aa s = (Success (enc aa), s') ∧
  good_table enc n s'`,
  rw[]>>fs[lookup_insert_table_def]>>
  simp msimps>>
  reverse IF_CASES_TAC
  >- (
    fs[good_table_def]>>
    rfs[])>>
  simp[]>>
  TOP_CASE_TAC
  >- (
    fs[good_table_def]>>
    match_mp_tac IMP_EVERY_LUPDATE>>fs[]>>
    drule EL_MEM>>
    metis_tac[EVERY_MEM])
  >>
  fs[good_table_def]>>
  drule EL_MEM>>
  drule ALOOKUP_MEM>>
  fs[EVERY_MEM]>>
  rw[]>> first_x_assum drule>>
  disch_then drule>>
  fs[]);

val enc_line_hash_correct = Q.prove(`
  ∀line.
  good_table enc n s ∧ 0 < n ⇒
  ∃s'.
  enc_line_hash enc skip_len n line s =
  (Success (enc_line enc skip_len line),s') ∧
  good_table enc n s'`,
  Cases>>fs[enc_line_hash_def,enc_line_def]>>
  fs msimps>>
  qmatch_goalsub_abbrev_tac`lookup_insert_table _ _ aa`>>
  rw[]>>
  drule lookup_insert_table_correct>>rw[]>>simp[]);

val enc_line_hash_ls_correct = Q.prove(`
  ∀xs s.
  good_table enc n s ∧ 0 < n ⇒
  ∃s'.
  enc_line_hash_ls enc skip_len n xs s =
  (Success (MAP (enc_line enc skip_len) xs), s') ∧
  good_table enc n s'`,
  Induct>>fs[enc_line_hash_ls_def]>>
  fs msimps>>
  rw[]>> simp[]>>
  drule enc_line_hash_correct>>
  disch_then (qspec_then `h` assume_tac)>>rfs[]>>
  first_x_assum drule>>
  rw[]>>simp[]);

val enc_sec_hash_ls_correct = Q.prove(`
  ∀xs s.
  good_table enc n s ∧ 0 < n ⇒
  ∃s'.
  enc_sec_hash_ls enc skip_len n xs s =
  (Success (MAP (enc_sec enc skip_len) xs), s') ∧
  good_table enc n s'`,
  Induct>>fs[enc_sec_hash_ls_def]>>
  fs msimps>>
  rw[]>> simp[]>>
  TOP_CASE_TAC>>simp[]>>
  drule enc_line_hash_ls_correct>>
  simp[]>>
  disch_then(qspec_then`l` assume_tac)>>fs[]>>
  first_x_assum drule>>rw[]>>
  simp[enc_sec_def]);

Theorem enc_secs_correct`
  enc_secs enc n xs =
  (enc_sec_list enc xs)`
  (
  fs[enc_secs_def,enc_secs_aux_def]>>
  fs[fetch "-" "run_ienc_state_64_def",run_def]>>
  simp[enc_sec_hash_ls_full_def]>>
  qmatch_goalsub_abbrev_tac `_ enc sl nn xs s`>>
  qspecl_then [`sl`,`nn`,`enc`,`xs`,`s`] mp_tac (GEN_ALL enc_sec_hash_ls_correct)>>
  impl_tac>-
    (unabbrev_all_tac>>fs[good_table_def,EVERY_REPLICATE])>>
  rw[]>>
  fs[enc_sec_list_def]);

val _ = export_theory();
