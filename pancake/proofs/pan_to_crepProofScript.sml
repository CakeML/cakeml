(*
  Correctness proof for pan_simp
*)

open preamble
     pan_to_crepTheory
     panSemTheory crepSemTheory


val _ = new_theory "pan_to_crepProof";

val _ = set_grammar_ancestry ["pan_to_crep", "panSem", "crepSem"];

Datatype:
  context =
  <| var_nums : panLang$varname |-> shape # num list;
     dec_nums : panLang$varname |-> shape # num list|>
End

(*
(* may be not needed right now *)
Definition load_with_shape_def:
  load_with_shape One e = ([Load e], One) /\
  load_with_shape (Comb []) e =  ([Const 0w], One) /\
  load_with_shape (Comb shape:shapes) e =
End
*)

Definition cexp_list_def:
  (cexp_list [] _ = []) /\
  (cexp_list _ [] = []) /\
  (cexp_list (One::sh) (e::es) = [e] :: cexp_list sh es) /\
  (cexp_list (Comb sh::sh') es =
   let  es' = FLAT (cexp_list sh es) in
   es' :: cexp_list sh' (DROP (LENGTH es') es))
Termination
  cheat
End

(* using this style to avoid using HD for code extraction later *)
Definition cexp_heads_def:
  (cexp_heads [] = SOME []) /\
  (cexp_heads (e::es) =
   case (e,cexp_heads es)  of
   | [], _ => NONE
   | _ , NONE => NONE
   | x::xs, SOME ys => SOME (x::ys))
End


Definition cexp_heads_simp_def:
  cexp_heads_simp es =
  if (MEM [] es) then NONE
  else SOME (MAP HD es)
End


Theorem cexp_heads_eq:
  !es. cexp_heads es = cexp_heads_simp es
Proof
  Induct >>
  rw [cexp_heads_def, cexp_heads_simp_def] >>
  fs [] >>
  every_case_tac >> fs []
QED

(*
  (compile_exp ctxt (Op bop es) =
   let cexps = MAP FST (MAP (compile_exp ctxt) es) in
   if (MEM [] cexps) then ([Const 0w], One)
   else ([Op bop (MAP HD cexps)], One)) /\
*)

Definition load_shape_def:
  (load_shape One e = [Load e]) /\
  (load_shape (Comb shp) e = load_shapes shp e) /\

  (load_shapes [] _ =  []) /\
  (load_shapes (sh::shs) e =
   load_shape sh e ++ load_shapes shs (Op Add [e; Const byte$bytes_in_word]))
End

Definition compile_exp_def:
  (compile_exp ctxt ((Const c):'a panLang$exp) =
   ([(Const c): 'a crepLang$exp], One)) /\
  (compile_exp ctxt (Var vname) =
   case FLOOKUP ctxt.var_nums vname of
   | SOME (shape, []) => ([Const 0w], One) (* TODISC: to avoid MAP [] *)
   | SOME (shape, ns) => (MAP Var ns, shape)
   | NONE => ([Const 0w], One)) /\
  (compile_exp ctxt (Label fname) = ([Label fname], One)) /\
  (compile_exp ctxt (Struct es) =
   let cexps = MAP (compile_exp ctxt) es in
   case cexps of
   | [] =>  ([Const 0w], One) (* TODISC: to avoid MAP [], although this cannot happen *)
   | ces => (FLAT (MAP FST ces), Comb (MAP SND ces))) /\
  (compile_exp ctxt (Field index e) =
   let (cexp, shape) = compile_exp ctxt e in
   case shape of
   | One => ([Const 0w], One)
   | Comb shapes =>
     if index < LENGTH shapes then
     (case cexp of
      | [] => ([Const 0w], One)
      (* TODISC: to avoid [] from cexp_list, although this cannot happen *)
      | ce => (EL index (cexp_list shapes ce), EL index shapes))
      else ([Const 0w], One)) /\
  (compile_exp ctxt (Load sh e) =
   let (cexp, shape) = compile_exp ctxt e in
   case cexp of
   | [] => ([Const 0w], One) (* TODISC: to avoid using HD *)
   | e::es => (load_shape sh e, sh)) /\ (* TODISC: what shape should we emit? *)
  (compile_exp ctxt (LoadByte e) =
   let (cexp, shape) = compile_exp ctxt e in
   case cexp of
   | [] => ([Const 0w], One)  (* TODISC: to avoid using HD *)
   | e::es => ([LoadByte e], One)) /\
  (compile_exp ctxt (Op bop es) =
   let cexps = MAP FST (MAP (compile_exp ctxt) es) in
   case cexp_heads cexps of
   | SOME (e::es) => ([Op bop (e::es)], One) (* TODISC: to avoid [], and MAP [] *)
   | _ => ([Const 0w], One)) /\
  (compile_exp ctxt (Cmp cmp e e') =
   let ce  = FST (compile_exp ctxt e);
       ce' = FST (compile_exp ctxt e') in
   case (ce, ce') of
   | (e::es, e'::es') => ([Cmp cmp e e'], One)
   | (_, _) => ([Const 0w], One)) /\
  (compile_exp ctxt (Shift sh e n) = (* TODISC: to avoid [], and MAP [] *)
   case FST (compile_exp ctxt e) of
   | [] => ([Const 0w], One)
   | e::es => ([Shift sh e n], One))
Termination
  cheat
End


(* assoc? *)
Definition list_seq_def:
  (list_seq [] = (Skip:'a crepLang$prog)) /\
  (list_seq [e] = e) /\
  (list_seq (e::e'::es) = Seq e (list_seq (e::es)))
End


Definition store_cexps_def:
  (store_cexps [] _ = []) /\
  (store_cexps (e::es) ad =
   [Store ad e] ++
   store_cexps es (Op Add [ad; Const byte$bytes_in_word]))
End

(*
  look into the context for v, if v is already an assigned variable,
  take it and store it in dec_nums, see the last conunter in the domain of
  context, and rewrite v to store shape + these numbers *)

Definition declare_ctxt:
  declare_ctxt ctxt v es shape = ARB
End

Definition compile_prog_def:
  (compile_prog _ (Skip:'a panLang$prog) = (Skip:'a crepLang$prog)) /\
  (compile_prog ctxt (Dec v e p) =
   Seq
   (compile_prog (declare_ctxt ctxt v (FST(compile_exp ctxt e)) (SND(compile_exp ctxt e))) p)
   ARB  (* list of assign instructions to restore the previously assigned value of v *)) /\
  (compile_prog ctxt (Assign vname e) =  (* TODISC: shape check? *)
   case (FLOOKUP ctxt.var_nums vname, compile_exp ctxt e) of
   | SOME (One, n::ns), (cexp::cexps, One) => Assign n cexp
   | SOME (Comb shapes, ns), (cexps, Comb shapes') =>
     if LENGTH ns = LENGTH cexps
     then list_seq (MAP2 Assign ns cexps)
     else Skip
   | _ => Skip) /\
  (compile_prog ctxt (Store dest src) =
   case (compile_exp ctxt dest, compile_exp ctxt src) of
   | (ad::ads, One), (e::es, One) => Store ad e
   | (ad::ads, One), (es, Comb shapes) =>
  (* TODISC: is it to dump es to memory like that? *)
     list_seq (store_cexps es ad)
   | _ => Skip) /\
  (compile_prog ctxt (StoreByte dest src) =
   case (compile_exp ctxt dest, compile_exp ctxt src) of
   | (ad::ads, One), (e::es, One) => StoreByte ad e
   | _ => Skip) /\
  (compile_prog ctxt (Seq p p') =
   Seq (compile_prog ctxt p) (compile_prog ctxt p')) /\
  (compile_prog ctxt (If e p p') =
   case compile_exp ctxt e of
   | (cexp::cexps, One) =>
     If cexp (compile_prog ctxt p) (compile_prog ctxt p')
   | _ => Skip) /\
  (compile_prog ctxt (While e p) =
   case compile_exp ctxt e of
   | (cexp::cexps, One) =>
     While cexp (compile_prog ctxt p)
   | _ => Skip) /\
  (compile_prog ctxt Break = Break) /\
  (compile_prog ctxt Continue = Continue) /\
  (compile_prog ctxt (Call rt e es) = ARB) /\
  (compile_prog ctxt (ExtCall f v1 v2 v3 v4) = ARB) /\
  (compile_prog ctxt (Raise e) = ARB) /\
  (compile_prog ctxt (Return e) = ARB) /\
  (compile_prog ctxt Tick = Tick)
End

val s = ``(s:('a,'ffi) panSem$state)``

Definition state_rel_def:
  state_rel ^s (t:('a,'ffi) crepSem$state) <=>
  s.memory = t.memory /\
  s.memaddrs = t.memaddrs /\
  s.clock = t.clock /\
  s.be = t.be /\
  s.ffi = t.ffi
End

Definition locals_rel_def:
  locals_rel (ctxt:context) l l' = ARB
End

Definition code_rel_def:
  code_rel (ctxt:context) l l' = ARB
End

Definition assigned_vars_def:
  assigned_vars p l = ARB
End

Definition evals_def:
  (evals (s:('a,'ffi) crepSem$state) [] = []) /\
  (evals s (e::es) = eval s e :: evals s es)
End


Theorem compile_exp_correct:
  !s t ctxt e v es sh.
  state_rel s t /\
  locals_rel ctxt s t /\
  eval s e = SOME v /\
  compile_exp ctxt e = (es, sh) ==>
  flatten_func v = evals t es
  (* may be to do cases on v, if it is a word, or a label or a struct,
     but may be not  *)
Proof
  cheat
QED

val goal =
  ``λ(prog, s). ∀res s1 t ctxt.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ locals_rel ctxt s.locals t.locals ∧
      assigned_vars prog FEMPTY ⊆ FDOM (ctxt.var_nums) ⇒
      ∃res1 t1. evaluate (compile_prog ctxt prog,t) = (res1,t1) /\
      state_rel s1 t1 ∧
      case res of
       | NONE => res1 = NONE /\ locals_rel ctxt s1.locals t1.locals
       | SOME (Return v) => res1 = SOME (Return (ARB v)) (* many return values *)
       | SOME Break => res1 = SOME Break
       | SOME Continue => res1 = SOME Continue (* need to think *)
       | SOME TimeOut => res1 = SOME TimeOut   (* need to think *)
       | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
       | SOME (Exception v) => res1 = SOME (Exception (ARB v))
       | _ => F``

local
  val ind_thm = panSemTheory.evaluate_ind
    |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem compile_Skip:
  ^(get_goal "comp _ panLang$Skip")
Proof
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def, crepSemTheory.evaluate_def,
      compile_prog_def] >> rveq >> fs []
QED

Theorem compile_Dec:
  ^(get_goal "comp _ (panLang$Dec _ _ _)")
Proof
 cheat
QED


val _ = export_theory();
