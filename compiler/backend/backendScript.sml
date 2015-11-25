open preamble
     source_to_modTheory
     mod_to_conTheory
     con_to_decTheory
     dec_to_exhTheory
     exh_to_patTheory
     pat_to_closTheory
     clos_to_bvlTheory
     bvl_to_bviTheory
     bvi_to_bvpTheory
     bvp_to_wordTheory
     word_to_stackTheory
     stack_to_labTheory
     lab_to_targetTheory

val _ = new_theory"backend";

val _ = Datatype`config =
  <| source_conf : source_to_mod$config
   ; mod_conf : mod_to_con$config
   ; clos_conf : clos_to_bvl$config
   ; bvl_conf : num (* no idea what this number represents *)
   ; bvp_conf : bvp_to_word$config
   ; stack_conf : stack_to_lab$config
   ; lab_conf : 'a lab_to_target$config
   ; asm_conf : 'a asm_config
   |>`;

val source_to_mod_def = Define`
  source_to_mod c p =
    let (c',p) = source_to_mod$compile c.source_conf p in
    let c = c with source_conf := c' in
    (c,p)`;

val source_to_con_def = Define`
  source_to_con c p =
  let (c,p) = source_to_mod c p in
  let (c',p) = mod_to_con$compile c.mod_conf p in
  let c = c with mod_conf := c' in
  (c,p)`;

val source_to_dec_def = Define`
  source_to_dec c p =
  let (c,p) = source_to_con c p in
  let (n,e) = con_to_dec$compile c.source_conf.next_global p in
  let c = c with source_conf updated_by (λc. c with next_global := n) in
  (c,e)`;

val source_to_exh_def = Define`
  source_to_exh c p =
  let (c,e) = source_to_dec c p in
  let e = dec_to_exh$compile_exp c.mod_conf.exh_ctors_env e in
  (c,e)`;

val source_to_pat_def = Define`
  source_to_pat c p =
  let (c,e) = source_to_exh c p in
  let e = exh_to_pat$compile e in
  (c,e)`;

val source_to_clos_def = Define`
  source_to_clos c p =
  let (c,e) = source_to_pat c p in
  let e = pat_to_clos$compile e in
  (c,e)`;

val source_to_bvl_def = Define`
  source_to_bvl c p =
  let (c,e) = source_to_clos c p in
  let (c',p) = clos_to_bvl$compile c.clos_conf e in
  let c = c with clos_conf := c' in
  (c,p)`;

val source_to_bvi_def = Define`
  source_to_bvi c p =
  let (c,p) = source_to_bvl c p in
  let (s,p,c') = bvl_to_bvi$compile_prog c.clos_conf.start c.bvl_conf p in
  let c = c with <| clos_conf updated_by (λc. c with start := s)
                  ; bvl_conf := c' |> in
  (c,p)`;

val source_to_bvp_def = Define`
  source_to_bvp c p =
  let (c,p) = source_to_bvi c p in
  let p = bvi_to_bvp$compile_prog p in
  (c,p)`;

val source_to_word_def = Define`
  source_to_word c p =
  let (c,p) = source_to_bvp c p in
  let p = bvp_to_word$compile c.bvp_conf p in
  (c,p)`;

val source_to_stack_def = Define`
  source_to_stack c p =
  let (c,p) = source_to_word c p in
  let p = word_to_stack$compile c.clos_conf.start c.asm_conf p in
  (c,p)`;

val source_to_lab_def = Define`
  source_to_lab c p =
  let (c,p) = source_to_stack c p in
  let p = stack_to_lab$compile c.clos_conf.start c.stack_conf p in
  (c,p)`;

val source_to_target_def = Define`
  source_to_target c p =
  let (c,p) = source_to_lab c p in
  let b = lab_to_target$compile c.asm_conf c.lab_conf p in
  OPTION_MAP (λb. (b,c)) b`;

val compile_def = Define`
  compile c p =
    let (c',p) = source_to_mod$compile c.source_conf p in
    let c = c with source_conf := c' in
    let (c',p) = mod_to_con$compile c.mod_conf p in
    let c = c with mod_conf := c' in
    let (n,e) = con_to_dec$compile c.source_conf.next_global p in
    let c = c with source_conf updated_by (λc. c with next_global := n) in
    let e = dec_to_exh$compile_exp c.mod_conf.exh_ctors_env e in
    let e = exh_to_pat$compile e in
    let e = pat_to_clos$compile e in
    let (c',p) = clos_to_bvl$compile c.clos_conf e in
    let c = c with clos_conf := c' in
    let (s,p,c') = bvl_to_bvi$compile_prog c.clos_conf.start c.bvl_conf p in
    let c = c with <| clos_conf updated_by (λc. c with start := s)
                    ; bvl_conf := c' |> in
    let p = bvi_to_bvp$compile_prog p in
    let p = bvp_to_word$compile c.bvp_conf p in
    let p = word_to_stack$compile c.clos_conf.start c.asm_conf p in
    let p = stack_to_lab$compile c.clos_conf.start c.stack_conf p in
    let b = lab_to_target$compile c.asm_conf c.lab_conf p in
    OPTION_MAP (λb. (b,c)) b`;

val compile_eq_source_to_target = Q.store_thm("compile_eq_source_to_target",
  `compile = source_to_target`,
  rw[FUN_EQ_THM,compile_def,
     source_to_target_def,
     source_to_lab_def,
     source_to_stack_def,
     source_to_word_def,
     source_to_bvp_def,
     source_to_bvi_def,
     source_to_bvl_def,
     source_to_clos_def,
     source_to_pat_def,
     source_to_exh_def,
     source_to_dec_def,
     source_to_con_def,
     source_to_mod_def] >>
  unabbrev_all_tac >>
  rpt (CHANGED_TAC (rw[] >> fs[] >> rw[] >> rfs[])));

val _ = export_theory();
