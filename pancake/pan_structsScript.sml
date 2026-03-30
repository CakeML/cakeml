(*
  Convert named structs to raw structs
*)
Theory pan_structs
Ancestors
  panLang backend_common
Libs
  preamble


val _ = numLib.prefer_num();


(* Context of shapes before conversion *)
Datatype:
  context =
  <| structs : (stcname # (fldname # shape) list) list
   ; locals  : (varname # shape) list
   ; globals : (varname # shape) list
  |>
End


(* Return index of x in alist *)
Definition afindi_def:
  afindi x [] = NONE /\
  afindi x ((k,v)::t) =
    if x = k then
      SOME 0
    else
      case afindi x t of
      | NONE => NONE
      | SOME i => SOME (1 + i)
End

(* Replace named struct shapes with raw structs *)
Definition compile_shape_def:
  (compile_shape sctxt One = One) ∧
  (compile_shape sctxt (Comb shapes) = Comb $ compile_shapes sctxt shapes) ∧
  (compile_shape sctxt (Named nm) =
    case dropWhile (\(n,fs). ~(n = nm)) sctxt of
    | (nm,flds)::sctxt' => Comb $ compile_shapes sctxt' $ MAP SND flds
    | _ => One (* should never happen *)) ∧
  (compile_shapes sctxt [] = []) ∧
  (compile_shapes sctxt (sh::shs) =
    compile_shape sctxt sh :: compile_shapes sctxt shs)
Termination
  wf_rel_tac
    ‘inv_image
      (* lexicographic combination of (struct info list size, shape/s size): *)
      (measure LENGTH
      LEX measure
        (\x. case x of
          | INL x => shape_size x
          | INR x => list_size shape_size x))
      (* getting pair from args: *)
      (\x. case x of
        | INL x => (FST x, INL $ SND x)
        | INR x => (FST x, INR $ SND x))’ >>
	rw[] >>
	disj1_tac >>
	irule LESS_LESS_EQ_TRANS >>
	irule_at Any LENGTH_dropWhile_LESS_EQ >>
  qmatch_asmsub_abbrev_tac `dropWhile ff` >>
  qexists `ff` >>
  rw[]
End

(* Returns unconverted shape of an expression *)
Definition old_exp_shape_def:
  (old_exp_shape ctxt (Var Local v) =
    case ALOOKUP ctxt.locals v of
    | NONE => One (* should never happen *)
    | SOME sh => sh) ∧
  (old_exp_shape ctxt (Var Global v) =
    case ALOOKUP ctxt.globals v of
    | NONE => One (* should never happen *)
    | SOME sh => sh) ∧
  (old_exp_shape ctxt (RStruct es) =
    Comb $ old_exp_shapes ctxt es) ∧
  (old_exp_shape ctxt (RField index e) =
    case old_exp_shape ctxt e of
    | Comb shs =>
      (case LLOOKUP shs index of
      | SOME sh => sh
      | NONE => One (* should never happen *))
    | _ => One (* should never happen *)) ∧
  (old_exp_shape ctxt (NStruct nm eflds) = Named nm) ∧
  (old_exp_shape ctxt (NField fld e) =
    (case old_exp_shape ctxt e of
    | Named nm =>
      (case ALOOKUP ctxt.structs nm of
      | SOME flds =>
        (case ALOOKUP flds fld of
        | SOME sh => sh
        | NONE => One (* should never happen *))
      | NONE => One (* should never happen *))
    | _ => One (* should never happen *))) ∧
  (old_exp_shape ctxt (Load sh e) = sh) ∧
  (old_exp_shape ctxt _ = One) ∧
  (old_exp_shapes ctxt [] = []) ∧
  (old_exp_shapes ctxt (e::es) =
      (old_exp_shape ctxt e)::(old_exp_shapes ctxt es))
Termination
  cheat (* TODO: replace cheat *)
End

(* Returns converted expression *)
Definition compile_exp_def:
  (compile_exp ctxt (RStruct es) =
    RStruct $ compile_exps ctxt es) ∧
  (compile_exp ctxt (RField index e) =
    RField index $ compile_exp ctxt e) ∧
  (compile_exp ctxt (NStruct nm eflds) =
    let es' =
      case ALOOKUP ctxt.structs nm of
      | SOME flds => compile_fields ctxt flds eflds
      | NONE => [] (* should never happen *) in
    RStruct es') ∧
  (compile_exp ctxt (NField fld e) =
    let e'= compile_exp ctxt e in
    let index =
      (case old_exp_shape ctxt e of
      | Named nm =>
        (case ALOOKUP ctxt.structs nm of
        | SOME flds =>
          (case afindi fld flds of
          | SOME i => i
          | NONE => 0 (* should never happen *))
        | NONE => 0 (* should never happen *))
      | _ => 0 (* should never happen *)) in
    RField index e') ∧
  (compile_exp ctxt (Load sh e) =
    Load (compile_shape ctxt.structs sh) (compile_exp ctxt e)) ∧
  (compile_exp ctxt (LoadByte e) =
    LoadByte (compile_exp ctxt e)) ∧
  (compile_exp ctxt (Load32 e) =
    Load32 (compile_exp ctxt e)) ∧
  (compile_exp ctxt (Op bop es) =
    Op bop (compile_exps ctxt es)) ∧
  (compile_exp ctxt (Panop pop es) =
    Panop pop (compile_exps ctxt es)) ∧
  (compile_exp ctxt (Cmp cmp e1 e2) =
    Cmp cmp (compile_exp ctxt e1) (compile_exp ctxt e2)) ∧
  (compile_exp ctxt (Shift sh e n) =
    Shift sh (compile_exp ctxt e) n) ∧
  (compile_exp ctxt e = e) ∧
  (compile_exps ctxt [] = []) ∧
  (compile_exps ctxt (e::es) =
      (compile_exp ctxt e)::(compile_exps ctxt es)) ∧
  (compile_fields ctxt [] _ = []) ∧
  (compile_fields ctxt ((fld,sh)::flds) eflds =
    case ALOOKUP eflds fld of
    | SOME exp =>
      (compile_exp ctxt exp)::(compile_fields ctxt flds eflds)
      (* (compile_exp ctxt exp)::(compile_fields ctxt flds (ADELKEY fld eflds))) *)
    | NONE => [] (* should never happen *))
Termination
  cheat (* TODO: replace cheat *)
End

(* Returns converted statement *)
Definition compile_def:
  (compile ctxt (Dec v s e p) =
    Dec v
      (compile_shape ctxt.structs s)
      (compile_exp ctxt e)
      (compile (ctxt with locals := (v,s)::ctxt.locals) p)) ∧
  (compile ctxt (Assign vk v e) =
    Assign vk v (compile_exp ctxt e)) ∧
  (compile ctxt (Store ad v) =
    Store (compile_exp ctxt ad) (compile_exp ctxt v)) ∧
  (compile ctxt (Store32 ad v) =
    Store32 (compile_exp ctxt ad) (compile_exp ctxt v)) ∧
  (compile ctxt (StoreByte dest src) =
    StoreByte (compile_exp ctxt dest) (compile_exp ctxt src)) ∧
  (compile ctxt (Seq p p') =
    Seq (compile ctxt p) (compile ctxt p')) ∧
  (compile ctxt (If e p p') =
    If (compile_exp ctxt e) (compile ctxt p) (compile ctxt p')) ∧
  (compile ctxt (While e p) =
    While (compile_exp ctxt e) (compile ctxt p)) ∧
  (compile ctxt (Call rtyp f es) =
    let cexps = compile_exps ctxt es in
      case rtyp of
      | NONE => Call NONE f cexps
      | SOME (tl, hdl) =>
        Call (SOME (tl,
            case hdl of
            | NONE => NONE
            | SOME (eid, evar, p) =>
              SOME (eid, evar, compile ctxt p)))
          f cexps) ∧
  (compile ctxt (DecCall v s f es p) =
    DecCall v
      (compile_shape ctxt.structs s) f
      (compile_exps ctxt es)
      (compile (ctxt with locals := (v,s)::ctxt.locals) p)) ∧
  (compile ctxt (ExtCall f ptr1 len1 ptr2 len2) =
    ExtCall f
      (compile_exp ctxt ptr1)
      (compile_exp ctxt len1)
      (compile_exp ctxt ptr2)
      (compile_exp ctxt len2)) ∧
  (compile ctxt (Return rt) =
    Return (compile_exp ctxt rt)) ∧
  (compile ctxt (Raise eid excp) =
    Raise eid (compile_exp ctxt excp)) ∧
  (compile ctxt (ShMemStore op r ad) =
   ShMemStore op (compile_exp ctxt r) (compile_exp ctxt ad)) ∧
  (compile ctxt (ShMemLoad op vk r ad) =
   ShMemLoad op vk r (compile_exp ctxt ad)) ∧
  (compile _ p = p)
End

(* Returns converted declaration - Names are removed *)
Definition compile_decs_def:
  (compile_decs ctxt [] = ([],ctxt)) ∧
  (compile_decs ctxt (Decl sh v e::ds) =
    let (ds', ctxt') = compile_decs (ctxt with globals := (v,sh)::ctxt.globals) ds in
    (Decl (compile_shape ctxt.structs sh) v (compile_exp ctxt e) ::ds',
      ctxt')) ∧
  (compile_decs ctxt (Function fi::ds) =
    let (ds', ctxt') = compile_decs ctxt ds in
    let params = fi.params in
    let fi' = fi with <|
        params updated_by (MAP (\(p,s). (p, compile_shape ctxt.structs s)))
      ; body   updated_by (compile (ctxt' with locals := params))
      ; return updated_by (compile_shape ctxt.structs) |> in
    (Function fi'::ds', ctxt')) ∧
  (compile_decs ctxt (Name nm flds::ds) =
    compile_decs ctxt ds)
End

(* Returns struct context *)
Definition get_names_def:
  (get_names ctxt [] = ctxt) ∧
  (get_names ctxt (Name nm flds::ds) =
    get_names (ctxt with structs := (nm,flds)::ctxt.structs) ds) ∧
  (get_names ctxt (_::ds) =
    get_names ctxt ds)
End

(* Returns converted program *)
Definition compile_top_def:
  compile_top decs =
    let ctxt = <| structs := []; locals := []; globals := [] |> in
    FST $ compile_decs (get_names ctxt decs) decs
End
