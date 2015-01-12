open HolKernel boolLib bossLib
open pat_to_closTheory bvlBytecodeTheory clos_to_bvlTheory clos_numberTheory clos_annotateTheory
val _ = new_theory "newcompiler"

val _ = Datatype`
 compiler_state =
  <| next_global : num
   ; globals_env : (modN, ( (varN, num)fmap)) fmap # (varN, num) fmap
   ; contags_env : num # tag_env # (num, (conN # tid_or_exn)) fmap
   ; exh : exh_ctors_env
   ; rnext_label : num
   ; next_loc : num
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
                      Stack (TagEq (block_tag+none_tag));
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
    let ct = fromAList (MAP (λ(p,e). (p,(2,e))) aux) in
    let (f,r) = bvl_bc_table real_inst_length cs.rnext_label ct in
    let r = bvl_bc f [] TCNonTail 0 r e in
    let r = (compile_print_top types m2 top r) in
    let cs = (<| next_global := n ; globals_env := (m1,m2) ; contags_env := c
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
    let ct = fromAList (MAP (λ(p,e). (p,(2,e))) aux) in
    let (f,r) = bvl_bc_table real_inst_length init_compiler_state.rnext_label ct in
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
    let (e,aux) = cComp [e] [] in
    let ct = fromAList (MAP (λ(p,e). (p,(2,e))) aux) in
    let (f,r) = bvl_bc_table real_inst_length cs.rnext_label ct in
    let r = bvl_bc f [] TCNonTail 0 r e in
    let cs = (<| next_global := n ; globals_env := (m1,m2) ; contags_env := c
              ; exh := exh ; rnext_label := r.next_label |>) in
      (cs, (emit r [Stack Pop]).out)`;

val _ = export_theory()
