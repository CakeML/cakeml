open HolKernel boolLib bossLib
open pat_to_closTheory bvlBytecodeTheory clos_to_bvlTheory clos_numberTheory clos_annotateTheory
open bvl_to_bviTheory;

val _ = new_theory "newcompiler"

(*

NAMING CONVENTION

  L_stubs takes an L_config and returns code in L+1 which is required
  for compilation from L to L+1.

  L_init takes a tuple (L_config, L+1_config, ...) and returns a pair:
   - a list of bytes that is the compiled L_stubs
   - initial compiler state for compilation from L, i.e.
       (L_compiler_state, L+1_compiler_state, ...)

  L_compile takes
   - L_code, and
   - a compiler state which is a tuple (L_compiler_state, L+1_compiler_state, ...)
  It returns
   - a list of bytes that is the compilation of L_code, and
   - a new compiler state (L_compiler_state, L+1_compiler_state, ...)

*)


(* bvi *)

val _ = Datatype `bvi_config = bvi_config_STATE`;
val _ = Datatype `bvi_compiler_state = bvi_compiler_STATE`;

val bvi_init_def = Define `
  bvi_init bvi_config = (ARB:word8 list, ARB:bvi_compiler_state)`;

val bvi_compile = Define `
  bvi_compile bvi_list s = (ARB:word8 list,ARB:bvi_compiler_state)`;

(* bvl *)

val _ = Datatype `bvl_config =
  <| bvi_config : bvi_config |>`;
val _ = Datatype `bvl_compiler_state =
  <| bvl_n : num;
     bvi_compiler_state : bvi_compiler_state |>`;

val bvl_stubs_def = Define `
  bvl_stubs (c:bvl_config) = []:bvi_exp list`;

val bvl_init_def = Define `
  bvl_init (c:bvl_config) =
    let (bytes1,s1) = bvi_init c.bvi_config in
    let (bytes2,s2) = bvi_compile (bvl_stubs c) s1 in
      (bytes1 ++ bytes2, <| bvl_n := 0; bvi_compiler_state := s2 |>)`;

val bvl_compile_def = Define `
  bvl_compile (xs:bvl_exp list) (s:bvl_compiler_state) =
    let (bvi_list, aux, n) = bComp s.bvl_n xs in
    let (bytes,s1) = bvi_compile bvi_list s.bvi_compiler_state in
      (bytes,<| bvl_n := n; bvi_compiler_state := s1 |>)`;

(* clos *)

val _ = Datatype `clos_config =
  <| bvl_config : bvl_config |>`;
val _ = Datatype `clos_compiler_state =
  <| bvl_compiler_state : bvl_compiler_state |>`;

val clos_stubs_def = Define `
  clos_stubs (c:clos_config) = []:bvl_exp list`;

val clos_init_def = Define `
  clos_init (c:clos_config) =
    let (bytes1,s1) = bvl_init c.bvl_config in
    let (bytes2,s2) = bvl_compile (clos_stubs c) s1 in
      (bytes1 ++ bytes2, <| bvl_compiler_state := s2 |>)`;

val clos_compile_def = Define `
  clos_compile (xs:clos_exp list) (s:clos_compiler_state) =
    let (bvl_list, aux) = cComp xs [] in
    (* the following two lines are wrong *)
    let (bytes1,s1) = bvl_compile (MAP (SND o SND) aux) s.bvl_compiler_state in
    let (bytes2,s2) = bvl_compile bvl_list s1 in
      (bytes1 ++ bytes2,<| bvl_compiler_state := s2 |>)`;

(* --- *)

val _ = Datatype`
 compiler_state =
  <| next_global : num
   ; globals_env : (modN, ( (varN, num)fmap)) fmap # (varN, num) fmap
   ; contags_env : num # tag_env # (num, (conN # tid_or_exn)) fmap
   ; exh : exh_ctors_env
   ; rnext_label : num
   ; next_loc : num
   ; next_addr : num
   |>`;

val compile_print_vals_def = Define `
  (compile_print_vals [] _ s = s) /\
  (compile_print_vals ((x,((_:num),t))::types) map s =
  (let ty = (inf_type_to_string t) in
    let s = (emit s (MAP PrintC (EXPLODE (CONCAT ["val ";x;":"; ty;" = "])))) in
    let s = (emit s [Gread (fapply( 0) x map)]) in
    let s = (emit s (if t = (Infer_Tapp [] TC_word8)
                      then (MAP PrintC (EXPLODE "0wx"))++[PrintWord8]
                    else if t = (Infer_Tapp [] TC_char)
                      then (MAP PrintC (EXPLODE "#"))++[
                        Stack (PushInt(( 1 : int))); Stack(Cons string_tag); Print]
                    else [Print])) in
    let s = (emit s (MAP PrintC (EXPLODE "\n"))) in
      compile_print_vals types map s))`;

val compile_print_ctors_def = Define`
  (compile_print_ctors [] s = s) /\
  (compile_print_ctors ((c,_)::cs) s =
  (compile_print_ctors cs
      (emit s (MAP PrintC (EXPLODE (CONCAT [c;" = <constructor>\n"]))))))`;

val compile_print_types_def = Define `
  (compile_print_types [] s = s) /\
  (compile_print_types ((_,_,cs)::ts) s =
  (compile_print_types ts (compile_print_ctors (REVERSE cs) s)))`;

val compile_print_dec_def = Define `
  (compile_print_dec _ _ (Dtype _) s = s) /\
  (compile_print_dec _ _ (Dexn _ _) s = s) /\
  (compile_print_dec types map _ s = (compile_print_vals types map s))`;

val compile_print_err_def = Define `
  (compile_print_err cs =
  (let (cs,n) = (get_label cs) in
    let cs = (emit cs [Stack (Load( 0));
    (* TODO: need block_tag+1 here because clos->bvl increments all tags unnecessarily *)
                      Stack (TagEq (block_tag+1+none_tag));
                      JumpIf (Lab n);
                      Stack (PushInt(( 0 : int)));
                      Stack El]) in
    let cs = (emit cs (MAP PrintC (EXPLODE "raise "))) in
    let cs = (emit cs [Print]) in
    let cs = (emit cs (MAP PrintC (EXPLODE "\n"))) in
    let cs = (emit cs [Stop F; Label n; Stack Pop]) in
    cs))`;

val compile_print_top_def = Define `
 (compile_print_top types map top cs =
  (let cs = (compile_print_err cs) in
    let cs = ((case types of NONE => cs | SOME types =>
      (case top of
        (Tmod mn _ _) =>
          let str = (CONCAT["structure ";mn;" = <structure>\n"]) in
          emit cs (MAP PrintC (EXPLODE str))
      | (Tdec dec) => compile_print_dec types map dec cs))) in
    emit cs [Stop T]))`;

val compile_top_def = Define `
  compile_top types cs top =
    let n = cs.next_global in
    let (m10,m20) = cs.globals_env in
    let (u,m1,m2,p) = top_to_i1 n m10 m20 top in
    let (c,exh,p) = prompt_to_i2 cs.contags_env p in
    let (n,e) = prompt_to_i3 (none_tag, SOME (TypeId (Short "option")))
                   (some_tag, SOME (TypeId (Short "option"))) n p in
    let exh = FUNION exh cs.exh in
    let e = exp_to_exh exh e in
    let e = exp_to_pat [] e in
    let e = pComp e in
    let (l,e) = renumber_code_locs cs.next_loc e in
    let (e,aux) = cComp (cAnnotate 0 [e]) [] in
    let ct = fromAList aux in
    let (f,r) = bvl_bc_table real_inst_length cs.next_addr cs.rnext_label ct in
    let r = bvl_bc f [] TCNonTail 0 r e in
    let r = (compile_print_top types m2 top r) in
    let cs = (<| next_global := n ; globals_env := (m1,m2) ; contags_env := c
               ; next_addr := cs.next_addr + next_addr real_inst_length r.out
               ; next_loc := l ; exh := exh ; rnext_label := r.next_label |>) in
    (cs, (cs with globals_env := (m1,m20)), r.out)`;

val compile_prog_def = Define `
  compile_prog init_compiler_state prog =
    let n = init_compiler_state.next_global in
    let (m1,m2) = init_compiler_state.globals_env in
    let (u1,u2,m2,p) = prog_to_i1 n m1 m2 prog in
    let (u3,exh,p) = prog_to_i2 init_compiler_state.contags_env p in
    let (u4,e) = prog_to_i3 (none_tag, SOME (TypeId (Short "option")))
                   (some_tag, SOME (TypeId (Short "option"))) n p in
    let e = exp_to_exh (FUNION exh init_compiler_state.exh) e in
    let e = exp_to_pat [] e in
    let e = pComp e in
    let (l,e) = renumber_code_locs init_compiler_state.next_loc e in
    let (e,aux) = cComp (cAnnotate 0 [e]) [] in
    let ct = fromAList aux in
    let (f,r) = bvl_bc_table real_inst_length init_compiler_state.next_addr init_compiler_state.rnext_label ct in
    let r = bvl_bc f [] TCNonTail 0 r e in
    let r = compile_print_err r in
    let r = case FLOOKUP m2 "it" of NONE => r
               | SOME n => let r = (emit r [Gread n; Print]) in
                           emit r (MAP PrintC (EXPLODE "\n")) in
    let r = (emit r [Stop T]) in
      REVERSE r.out`;

(* special entrypoints *)

val compile_special_def = Define `
 compile_special cs top =
   let n = cs.next_global in
   let (m1,m2) = cs.globals_env in
   let (u1,u2,u3,p) = top_to_i1 n m1 m2 top in
   let (u4,exh,p) = prompt_to_i2 cs.contags_env p in
   let e = decs_to_i3 n (case p of Prompt_i2 ds => ds) in
   let exh = FUNION exh cs.exh in
   let e = exp_to_exh exh e in
   let e = exp_to_pat [] e in
   let e = pComp e in
   let (e,u5) = cComp [e] [] in
   let r = bvl_bc LN [] TCNonTail 0 <|out:=[]; next_label:=cs.rnext_label|> e in
     (emit r [Stack Pop; Stop T]).out`;

val prompt_to_i3_initial_def = Define `
 prompt_to_i3_initial next (Prompt_i2 ds) =
  let n = (num_defs ds) in
    ((next+n), Let_i2 NONE (Extend_global_i2 n) (decs_to_i3 next ds))`;

val prog_to_i3_initial_def = Define `
 (prog_to_i3_initial next [] = (next, Lit_i2 Unit)) /\
 (prog_to_i3_initial next (p::ps) =
  let (next,p) = prompt_to_i3_initial next p in
  let (next',ps) = prog_to_i3_initial next ps in
    (next', Let_i2 NONE p ps))`;

val compile_initial_prog_def = Define `
  compile_initial_prog cs prog =
    let n = cs.next_global in
    let (m1,m2) = cs.globals_env in
    let (u,m1,m2,p) = prog_to_i1 n m1 m2 prog in
    let (c,exh,p) = prog_to_i2 cs.contags_env p in
    let (n,e) = prog_to_i3_initial n p in
    let exh = FUNION exh cs.exh in
    let e = exp_to_exh exh e in
    let e = exp_to_pat [] e in
    let e = pComp e in
    let (l,e) = renumber_code_locs cs.next_loc e in
    let (e,aux) = cComp (cAnnotate 0 [e]) [] in
    let ct = fromAList aux in
    let (f,r) = bvl_bc_table real_inst_length cs.next_addr cs.rnext_label ct in
    let r = bvl_bc f [] TCNonTail 0 r e in
    let r = emit r [Stack Pop] in
    let cs = (<| next_global := n ; globals_env := (m1,m2) ; contags_env := c
               ; next_addr := cs.next_addr + next_addr real_inst_length r.out
               ; next_loc := l; exh := exh ; rnext_label := r.next_label |>) in
      (cs, r.out)`;

val _ = export_theory()
