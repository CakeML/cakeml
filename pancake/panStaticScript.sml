(*
  Static checking for Pancake.

  General checks:
  - Errors:
    - Main function parameters
    - Exported main function
    - Exported function with >4 arguments
    - Missing function exit (return, tail call, etc)
    - Loop exit outside loop (break, continue)
    - Incorrect number of function arguments
    - Incorrect number of Op arguments (impossible from parser)
  - Warnings:
    - Unreachable statements (after function exit, after loop exit)
      - Note: To minimise output, subsequent warnings of this kind after the
        first guaranteed-unreachable line within a block are silenced. If an
        inner block occurs *before* this line, warnings within that block do not
        count towards this first. However, if an inner block occurs *after* this
        line, the line is recognised as the first for the inner block as well
    - Base-calculated address in shared memory operation
    - Non-base -calculated address in local memory operation

  Scope checks:
  - Errors:
    - Undefined/out-of-scope functions
    - Undefined/out-of-scope variables
    - Undefined/out-of-scope struct names
    - Redefined functions
    - Redefined function parameter names
    - Redefined struct names
    - Redefined struct field names
  - Warnings:
    - Redefined variables

  Shape checks:
  - Errors:
    - Mismatched variable declarations
    - Mismatched variable assignments
    - Mismatched function arguments
    - Mismatched function returns
    - Mismatched struct fields
    - Incorrect number of struct field values
    - Mismatched source/destination for memory operations
    - Non-word main function return declarations
    - Non-word FFI arguments
    - Non-word exported argument declarations
    - Non-word exported return declarations
    - Non-word addresses for memory operations
    - Non-word/mismatched operator operands
    - Non-word condition expressions
    - Invalid field index
    - Invalid field name
    - Returned shape size >32 words (TODO: raised shape size)
*)
Theory panStatic
Libs
  preamble
Ancestors
  errorLogMonad panLang mlmap mlint mllist


val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "errorLog";


(* Error categories for printing *)
Datatype:
  staterr = ScopeErr mlstring
          | WarningErr mlstring
          | GenErr mlstring
          | ShapeErr mlstring
End

(*
  Return type of static_check_* functions:
    (retval, proper error) error # warning list
*)
Type static_result = ``:('a, staterr) error # staterr list``

(*
  Exp-level state for references to @base
  "Priority": `Based` > `NotTrusted` > `Trusted` > `NotBased`
    where an exp can never have a lower priority state to its components,
    ie. an exp containing a `NotTrusted` exp can never be `Trusted` or `NotBased`
*)
Datatype:
  based =
    Based | NotBased  (* warned as appropriate *)
  | Trusted           (* excempt from warning *)
  | NotTrusted        (* always warned *)
End

(* Exp-level state for shape-aware basedness *)
Datatype:
  shaped_based =
    WordB   based
  | StructB (shaped_based list)
  | NamedB  stcname ((fldname # shaped_based) list)
End

(*
  Prog-level state for reachability
  Possible transitions are linear: `IsReach` -> `WarnReach` -> `NotReach`
    where `NotReach` only comes after a reachability warning
*)
Datatype:
  reachable =
    IsReach | NotReach  (* as named *)
  | WarnReach           (* "unreachable but has a pending warning" *)
End

(* Prog-level state for exit-ness of final statement *)
Datatype:
  last_stmt =
    RetLast | RaiseLast | TailLast  (* function exit *)
  | BreakLast | ContLast            (* loop exit *)
  | CondExitLast                    (* ambiguous exit (after conditionals) *)
  | InvisLast | OtherLast           (* non-exit *)
End

(* Type for function state *)
Datatype:
  func_info = <|
    ret_shape : shape                  (* shape of return value *)
  ; params    : (varname # shape) list (* parameter info *)
  |>
End

(* Type for local var state *)
Datatype:
  local_info = <|
    vsh_bd : shaped_based (* shaped basedness of var *)
  |>
End

(* Type for global var state *)
Datatype:
  global_info = <|
    vshape : shape (* shape of var *)
  |>
End

(* Type for error scope *)
Datatype:
  scope =
    FunScope  funname mlstring  (* in a function, possibly more specific *)
  | DeclScope varname           (* in a global declaration *)
  | StcScope  stcname fldname   (* in a struct name declaration *)
  | TopLevel
End

(* Record for current (per-func) context *)
Datatype:
  context = <|
    locals       : (varname , local_info ) map  (* tracked var state *)
  ; globals      : (varname , global_info) map  (* declared globals *)
  ; funcs        : (funname , func_info  ) map  (* all function info *)
  ; structs      : (stcname # struct_info) list (* struct name context *)
  ; scope        : scope                        (* current scope info *)
  ; in_loop      : bool                         (* loop status *)
  ; is_reachable : reachable                    (* reachability *)
  ; last         : last_stmt                    (* exit-ness of last statement *)
  ; loc          : mlstring                     (* location string *)
  |>
End

(* Record for static_check_exp returns *)
Datatype:
  exp_return = <|
    sh_bd : shaped_based (* shaped basedness of exp *)
  |>
End

(* Record for static_check_exps returns *)
Datatype:
  exps_return = <|
    sh_bds : shaped_based list (* shaped basedness of exps *)
  |>
End

(* Record for static_check_prog returns *)
Datatype:
  prog_return = <|
    exits_fun  : bool                       (* func exit status for all paths *)
  ; exits_loop : bool                       (* loop exit status for all paths *)
  ; last       : last_stmt                  (* new exit-ness of last statement *)
  ; var_delta  : (varname, local_info) map  (* change in var state *)
  ; curr_loc   : mlstring                   (* latest location string *)
  |>
End

(* Varieties of identifiers that can be out of scope *)
Datatype:
  scoped_id = Var | Fun | Stc
End


(* Functions for `based` and `shaped_based` *)

(*
  Builds a shaped based from a given shape and single based
  USED ON PRE-CHECKED SHAPES ONLY (will never be NONE)
 *)
Definition sh_bd_from_sh_def:
  sh_bd_from_sh sctxt b One = SOME $ WordB b /\
  sh_bd_from_sh sctxt b (Comb shs) =
    (case OPT_MMAP (sh_bd_from_sh sctxt b) shs of
    | SOME sbs => SOME $ StructB sbs
    | NONE => NONE) /\
  sh_bd_from_sh sctxt b (Named nm) =
    (case dropWhile (\(n,i). ~(n = nm)) sctxt of
    | (nm,info)::sctxt' =>
      let (field_nms, field_shs) = UNZIP info.fields in
      (case OPT_MMAP (sh_bd_from_sh sctxt' b) field_shs of
      | SOME field_sbs => SOME $ NamedB nm $ ZIP (field_nms, field_sbs)
      | NONE => NONE)
    | _ => NONE)
Termination
  wf_rel_tac `measure LENGTH LEX measure (shape_size o SND)`
  >> rw []
  >> imp_res_tac (Q.prove (`dropWhile P xs = ys ==> LENGTH ys <= LENGTH xs`,
        metis_tac [LENGTH_dropWhile_LESS_EQ]))
  >> fs []
End

(* Builds a shaped based with the shape of a given shaped based and single based *)
Definition sh_bd_from_bd_def:
  sh_bd_from_bd b (WordB b') = WordB b /\
  sh_bd_from_bd b (StructB sbs) = StructB $ MAP (sh_bd_from_bd b) sbs /\
  sh_bd_from_bd b (NamedB nm flds) =
    NamedB nm $ MAP (\(nm, sb). (nm, sh_bd_from_bd b sb)) flds
End

(* Determine if shaped based has a given shape *)
Definition sh_bd_has_shape_def:
  (sh_bd_has_shape sh sb =
    case (sh, sb) of
    | (One, WordB b) => T
    | (Comb shs, StructB sbs) => sh_bd_has_shape_list shs sbs
    | (Named nm, NamedB nm' flds) => nm = nm'
    | _ => F) /\
  (sh_bd_has_shape_list [] [] = T) /\
  (sh_bd_has_shape_list (sh::shs) [] = F) /\
  (sh_bd_has_shape_list [] (sb::sbs) = F) /\
  sh_bd_has_shape_list (sh::shs) (sb::sbs) =
    (sh_bd_has_shape sh sb /\ sh_bd_has_shape_list shs sbs)
End

(* Determine if two shaped baseds have the same shape *)
Definition sh_bd_eq_shapes_def:
  (sh_bd_eq_shapes sb sh =
    case (sb, sh) of
    | (WordB b, WordB b') => T
    | (StructB sbs, StructB sbs') => sh_bd_eq_shapes_list sbs sbs'
    | (NamedB nm flds, NamedB nm' flds') => nm = nm'
    | _ => F) /\
  (sh_bd_eq_shapes_list [] [] = T) /\
  (sh_bd_eq_shapes_list (sb::sbs) [] = F) /\
  (sh_bd_eq_shapes_list [] (sb::sbs) = F) /\
  sh_bd_eq_shapes_list (sb::sbs) (sb'::sbs') =
    (sh_bd_eq_shapes sb sb' /\ sh_bd_eq_shapes_list sbs sbs')
End

(* Lookup shaped basedness at a certain struct index *)
Definition index_sh_bd_def:
  index_sh_bd i (WordB b) = NONE ∧
  index_sh_bd i (StructB sbs) = LLOOKUP sbs i ∧
  index_sh_bd i (NamedB nm flds) = NONE
End

(* Lookup shaped basedness at a certain struct field *)
Definition field_sh_bd_def:
  field_sh_bd fld (WordB b) = NONE ∧
  field_sh_bd fld (StructB sbs) = NONE ∧
  field_sh_bd fld (NamedB nm flds) = ALOOKUP flds fld
End

(* Merge basedness according to priority *)
Definition based_merge_def:
  based_merge x y =
    case (x,y) of
    | (Based, _) => Based
    | (_, Based) => Based
    | (NotTrusted, _) => NotTrusted
    | (_, NotTrusted) => NotTrusted
    | (Trusted, _) => Trusted
    | (_, Trusted) => Trusted
    | (NotBased, NotBased) => NotBased
End

(* Comparison for combining based-ness between If/While branches *)
Definition sh_bd_branch_def:
  sh_bd_branch x y = if x = y then x else sh_bd_from_bd NotTrusted x
End

(*
  Combine local var state deltas of If/While branches
    where states are either combined between the two deltas (if in both) or with
    prior context (if in just one)
  Needs extension with extension of `local_info` type
*)
Definition branch_loc_inf_def:
  branch_loc_inf vctxt x y =
    let x' =
      mapWithKey (\k v. v with <|
          vsh_bd :=
            (if ~(member k y) then
              case lookup vctxt k of
              | SOME v' => sh_bd_branch v.vsh_bd v'.vsh_bd
              | NONE => sh_bd_from_bd NotTrusted v.vsh_bd
            else v.vsh_bd)
        |>) x in
    let y' =
      mlmap$mapWithKey (\k v. v with <|
          vsh_bd :=
            (if ~(member k x) then
              case lookup vctxt k of
              | SOME v' => sh_bd_branch v.vsh_bd v'.vsh_bd
              | NONE => sh_bd_from_bd NotTrusted v.vsh_bd
            else v.vsh_bd)
        |>) y in
    mlmap$unionWith (\vx vy. vx with <|
        vsh_bd := sh_bd_branch vx.vsh_bd vy.vsh_bd
      |>) x' y'
End

(* Combine local var state deltas of Seq progs *)
Definition seq_loc_inf_def:
  seq_loc_inf x y = union y x
End

(* Get shape string from shaped based *)
Definition sh_bd_to_str_def:
  sh_bd_to_str (WordB b) = strlit "1" ∧
  sh_bd_to_str (StructB []) = strlit "{}" ∧ (* should never happen *)
  sh_bd_to_str (StructB (x::xs)) = concat (
    strlit "{" :: sh_bd_to_str x ::
    MAP (λx. strlit "," ^ x) (MAP sh_bd_to_str xs) ++
    [strlit "}"]) ∧
  sh_bd_to_str (NamedB nm flds) = nm
End


(* Functions for `last_stmt` and `reachable` *)

(*
  Get string name for statement exit-ness
  USED FOR PRINTING ASSOCIATED WARNINGS ONLY
*)
Definition last_to_str_def:
  last_to_str l =
    case l of
    | RetLast      => «return»
    | RaiseLast    => «raise»
    | TailLast     => «tail call»
    | BreakLast    => «break»
    | ContLast     => «continue»
    | CondExitLast => «exiting conditional»
    | _            => «»
End

(*
  Determine next reachability state for prog sequences based on current state
    and exit-ness
  Handles `IsReach` -> `WarnReach` transition
*)
Definition next_is_reachable_def:
  next_is_reachable r x =
    case r of
    | IsReach => if ~(x = InvisLast \/ x = OtherLast) then WarnReach else IsReach
    | _ => r
End

(* Determine whether reachability has decreased *)
Definition next_now_unreachable_def:
  next_now_unreachable r r' = (r = IsReach /\ ~(r' = IsReach))
End

(*
  Determine whether a prog that can trigger a reachability warning is reached,
    and return last exit-ness and update context if so
  Handles `WarnReach` -> `NotReach` transition
*)
Definition reached_warnable_def:
  reached_warnable s ctxt =
    case s of
    | Seq prog1 prog2 => (NONE, ctxt)
    | Tick            => (NONE, ctxt)
    | Annot str1 str2 => (NONE, ctxt)
    | _               =>
      if ctxt.is_reachable = WarnReach then
        (SOME ctxt.last, ctxt with is_reachable := NotReach)
      else (NONE, ctxt)
End

(*
  Determine exit-ness of branches, based on whether a definite func or loop exit
    occurred
*)
Definition branch_last_stmt_def:
  branch_last_stmt double_ret double_loop_exit =
    if (double_ret \/ double_loop_exit) then CondExitLast else OtherLast
End

(* Determine exit-ness of Seq'd progs by ignoring invisible exit-ness *)
Definition seq_last_stmt_def:
  seq_last_stmt x y = if y = InvisLast then x else y
End


(* Error message helpers *)

(* Get description of current scope *)
Definition get_scope_desc_def:
  get_scope_desc scope =
    case scope of
    | FunScope fname desc =>
      concat [strlit "function "; fname; desc]
    | DeclScope vname =>
      concat [«initialisation of global variable »; vname]
    | StcScope sname fld =>
      concat [
        strlit "declaration of field "; fld;
        strlit " in named struct "; sname]
    | TopLevel =>
      «top-level declaration»
End

(*
  Get message for out of scope identifiers
  id_type :scoped id
*)
Definition get_scope_msg_def:
  get_scope_msg id_type loc id scope =
    let id_desc =
      case id_type of
      | Var => strlit "variable "
      | Fun => strlit "function "
      | Stc => strlit "struct name " in
    concat [loc; id_desc; id;
      « is not in scope in »;
      get_scope_desc scope; «\n»]
End

(*
  Identifier names that the parser recognises as built-in primitives and
  desugars to Primitive in declaration and assignment RHS positions. Used by
  add_primitive_hint to produce a more helpful message when a lookup fails
  on one of these names; extend this list as new primitives are added.
*)
Definition primitive_idents_def:
  primitive_idents = [«__add_with_carry__»]
End

(*
  Append a hint to a function-not-in-scope error when fname is a built-in
  primitive identifier. The parser desugars such names to a Primitive in
  declaration and assignment RHS positions, so a function-name lookup failure
  means the name was used in a position where the primitive is not available
  (e.g. standalone call, tail-return) and no user-defined function of that
  name exists either.
*)
Definition add_primitive_hint_def:
  add_primitive_hint fname msg =
    if MEM fname primitive_idents
    then concat [msg;
           «  note: »; fname;
           « is a built-in primitive only available in »;
           «declaration or assignment RHS positions\n»]
    else msg
End

(*
  Get message for redefined identifiers
  id_type :scoped id
*)
Definition get_redec_msg_def:
  get_redec_msg id_type loc id scope =
    let id_desc =
      case id_type of
      | Var => strlit "variable "
      | Fun => strlit "function "
      | Stc => strlit "struct name " in
    concat [
      loc; id_desc; id;
      strlit " is redeclared in ";
      get_scope_desc scope; strlit "\n"]
End

(*
  Get message for memory op addresses
  is_local: local vs shared
  is_load: load vs store
  is_untrust: NotTrusted vs other
*)
Definition get_memop_msg_def:
  get_memop_msg is_local is_load is_untrust loc scope =
    let mem_type = if is_local then «local » else «shared » in
    let op_type  = if is_load  then «load »  else «store »  in
    let issue =
      case (is_local, is_untrust) of
      | (F, F) => «is »
      | (F, T) => «may be »
      | (T, F) => «is not »
      | (T, T) => «may not be » in
    concat [
      loc; mem_type; op_type;
      «address »; issue; «calculated from base in »;
      get_scope_desc scope; «\n»]
End

(*
  Get message for op argument number
  is_exact: exactly vs at least
*)
Definition get_oparg_msg_def:
  get_oparg_msg is_exact n_expected n_given loc op scope =
    let issue =
      if is_exact then strlit " only accepts "
      else strlit " requires at least " in
    concat [
      loc; strlit "operation "; op;
      issue; n_expected; strlit " operands, ";
      n_given; strlit " provided in ";
      get_scope_desc scope; strlit "\n"]
End

(* Get message for unreachable statement *)
Definition get_unreach_msg_def:
  get_unreach_msg loc last scope = concat [
    loc;
    strlit "unreachable statement(s) after "; last;
    strlit " in " ;
    get_scope_desc scope; strlit "\n"]
End

(*
  Get message for rogue loop exit
  is_break: break vs continue
*)
Definition get_rogue_msg_def:
  get_rogue_msg is_break loc scope =
    let stmt = if is_break then «break » else «continue » in
    concat [
      loc; stmt;
      strlit "statement outside loop in ";
      get_scope_desc scope; strlit "\n"]
End

(* Get message for non-word shape *)
Definition get_non_word_msg_def:
  get_non_word_msg desc sh_str loc scope = concat [
    loc; desc; strlit " has shape "; sh_str;
    strlit " instead of a word in ";
    get_scope_desc scope; strlit "\n"]
End

(* Get message for declared shape mismatch *)
Definition get_shape_mismatch_msg_def:
  get_shape_mismatch_msg desc sh_str_actual sh_str_expect loc scope = concat [
    loc; desc; strlit " has shape "; sh_str_actual;
    strlit " instead of declared shape "; sh_str_expect;
    strlit " in ";
    get_scope_desc scope; strlit "\n"]
End

Definition get_implementation_err_msg_def:
  get_implementation_err_msg desc loc scope = concat [
    loc; desc; strlit " in "; get_scope_desc scope; strlit "\n";
    strlit "this should never happen. please report to a compiler developer\n"]
End


(* Misc functions *)

(* Find the first element in a sorted list that is repeated *)
Definition first_repeat_def:
  first_repeat xs =
    case xs of
    | (x1::x2::xs) =>
        if x1 = x2 then SOME x1
        else first_repeat $ x2::xs
    | _ => NONE
End

(* Get string name for binary ops *)
Definition binop_to_str_def:
  binop_to_str op =
    case op of
    | Add => «Add»
    | Sub => «Sub»
    | And => «And»
    | Or  => «Or»
    | Xor => «Xor»
End

(* Get string name for Pancake ops *)
Definition panop_to_str_def:
  panop_to_str op =
    case op of
    | Mul => «Mul»
End

(* Get string name for Pancake primitives *)
Definition primop_to_str_def:
  primop_to_str pop =
    case pop of
    | AddCarry => «AddCarry»
End


(* Static check helpers *)

(* Check for out of scope func *)
Definition check_fun_name_def:
  check_fun_name ctxt fname =
    case lookup ctxt.funcs fname of
    | NONE => error (ScopeErr $
        add_primitive_hint fname (get_scope_msg Fun ctxt.loc fname ctxt.scope))
    | SOME f => return f
End

(* Check for out of scope global *)
Definition check_global_var_def:
  check_global_var ctxt vname =
    case lookup ctxt.globals vname of
    | NONE => error (ScopeErr $ get_scope_msg Var ctxt.loc vname ctxt.scope)
    | SOME v => return v
End

(* Check for out of scope local *)
Definition check_local_var_def:
  check_local_var ctxt vname =
    case lookup ctxt.locals vname of
    | NONE => error (ScopeErr $ get_scope_msg Var ctxt.loc vname ctxt.scope)
    | SOME v => return v
End

(* Check for redeclared variable *)
Definition check_redec_var_def:
  check_redec_var ctxt vname =
    case (lookup ctxt.locals vname, lookup ctxt.globals vname) of
    | (NONE, NONE) => return ()
    | _ => log (WarningErr $ get_redec_msg Var ctxt.loc vname ctxt.scope)
End

(* Check shapes of exported arguments *)
Definition check_export_params_def:
  check_export_params loc scope [] = return () /\
  check_export_params loc scope ((vname,shape)::ps) =
    if ~(shape = One) then
      error (ShapeErr $ get_non_word_msg (
          concat [strlit "exported function parameter "; vname]
        ) (shape_to_str shape) loc scope)
    else check_export_params loc scope ps
End

(* Check operand shape and return merged shaped basedness *)
Definition check_operands_def:
  check_operands ctxt op_str [] = return $ NotBased /\
  check_operands ctxt op_str (sb::sbs) =
    case sb of
    | WordB b =>
      do
        b' <- check_operands ctxt op_str sbs;
        return $ based_merge b b'
      od
    | _ => error (ShapeErr $ get_non_word_msg (
        concat [strlit "operation "; op_str; strlit " operand"]
      ) (sh_bd_to_str sb) ctxt.loc ctxt.scope)
End

(* Check args for AddCarry primitive and return result shaped basedness *)
Definition check_addcarry_args_def:
  check_addcarry_args ctxt sh_bds =
    do
      op_str <<- primop_to_str AddCarry;
      nargs <<- LENGTH sh_bds;
      if ~(nargs = 3)
        then error (GenErr $ get_oparg_msg T «3»
          (num_to_str nargs) ctxt.loc op_str ctxt.scope)
      else return ();
      b <- check_operands ctxt op_str sh_bds;
      return $ StructB [WordB b; WordB NotBased]
    od
End

(* Check for arg number and shape *)
Definition check_func_args_def:
  check_func_args ctxt fname params sh_bds =
    case (params, sh_bds) of
    (* check declared vs provided *)
    | ((p,s)::ps, sb::sbs) =>
      if ~(sh_bd_has_shape s sb) then
        error (ShapeErr $ get_shape_mismatch_msg (concat [
            «value for argument »; p;
            « given to function »; fname
          ]) (sh_bd_to_str sb) (shape_to_str s) ctxt.loc ctxt.scope)
      else check_func_args ctxt fname ps sbs
    (* no more provided args *)
    | ((p,s)::ps, []) => error (GenErr $ concat [
        ctxt.loc; strlit "argument "; p;
        strlit " for call to function "; fname;
        strlit " is missing in ";
        get_scope_desc ctxt.scope; strlit "\n"])
    (* no more declared params *)
    | ([], sb::sbs) => error (GenErr $ concat [
        ctxt.loc; strlit "extra arguments given to function "; fname;
        strlit " in ";
        get_scope_desc ctxt.scope; strlit "\n"])
    (* checks complete *)
    | ([], []) => return ()
End

(* Check all fields are given exactly one value and shape *)
Definition check_struct_fields_def:
  check_struct_fields ctxt sname fields fsbs =
    case (fields, fsbs) of
    (* check declared vs provided *)
    | ((fld,sh)::fss, fsbs) =>
      do
        (* check number of provided values *)
        sb <-
          case FILTER (\(fld',sb). fld = fld') fsbs of
          (* exactly one *)
          | [(fld,sb)] => return sb
          (* zero *)
          | [] => error (ShapeErr $ concat [
              ctxt.loc; strlit "missing field "; fld;
              strlit " in named struct "; sname;
              strlit " constant in ";
              get_scope_desc ctxt.scope; strlit "\n"])
          (* more than one *)
          | _ => error (ShapeErr $ concat [
              ctxt.loc; strlit "multiple values for field "; fld;
              strlit " in named struct "; sname;
              strlit " constant in ";
              get_scope_desc ctxt.scope; strlit "\n"]);
        (* check shape of provided value *)
        if ~(sh_bd_has_shape sh sb) then
          error (ShapeErr $ get_shape_mismatch_msg (concat [
              strlit "value for field "; fld;
              strlit " given to named struct "; sname
            ]) (sh_bd_to_str sb) (shape_to_str sh) ctxt.loc ctxt.scope)
        else check_struct_fields ctxt sname fss (ADELKEY fld fsbs)
      od
    (* no more declared fields *)
    | ([], fsb::fsbs) => error (GenErr $ concat [
        ctxt.loc; strlit "unexpected field "; FST fsb;
        strlit " given to named struct "; sname;
        strlit " in ";
        get_scope_desc ctxt.scope; strlit "\n"])
    (* checks complete *)
    | ([], []) => return ()
End

(* Check shape names in scope *)
Definition check_shape_def:
  check_shape sctxt loc scope One = return () /\
  check_shape sctxt loc scope (Comb shs) =
    check_shapes sctxt loc scope shs /\
  check_shape sctxt loc scope (Named nm) =
    (case ALOOKUP sctxt nm of
    | SOME flds => return ()
    | NONE => error (ScopeErr $ get_scope_msg Stc loc nm scope)) /\
  check_shapes sctxt loc scope [] = return () /\
  check_shapes sctxt loc scope (sh::shs) =
    do
      check_shape sctxt loc scope sh;
      check_shapes sctxt loc scope shs
    od
End

(* Check field/param shape *)
Definition check_id_shapes_def:
  check_id_shapes sctxt loc scope [] =
    return () /\
  check_id_shapes sctxt loc scope ((id,shape)::ids) =
    do
      (* setup specific scope message *)
      scope' <-
        case scope of
        | FunScope fname _ =>
          return $ FunScope fname (concat [strlit " parameter "; id])
        | StcScope sname _ =>
          return $ StcScope sname id
        (* should never occur if static checker implemented correctly *)
        | s => error (GenErr $ get_implementation_err_msg
            (strlit "parameter or field found in unexpected scope")
            loc scope);
      check_shape sctxt loc scope' shape;
      check_id_shapes sctxt loc scope ids
    od
End


(* Main static checking functions *)

(*
  static_check_exp returns:
    (exp info (:exp_return)) static_result
  static_check_exps returns:
    (exps info (:exps_return)) static_result
*)
Definition static_check_exp_def:
  static_check_exp ctxt (Const num) =
    (* return exp info *)
    return <| sh_bd := WordB NotBased |> ∧
  static_check_exp ctxt (Var Local vname) =
    do
      (* check for out of scope var *)
      vinf <- check_local_var ctxt vname;
      (* return stored info *)
      return <| sh_bd := vinf.vsh_bd |>
    od ∧
  static_check_exp ctxt (Var Global vname) =
    do
      (* check for out of scope var *)
      vinf <- check_global_var ctxt vname;
      case sh_bd_from_sh ctxt.structs Trusted vinf.vshape of
      (* return exp info with stored shape *)
      | SOME sb => return <| sh_bd := sb |>
      (* should never occur if static checker implemented correctly *)
      | NONE => error (ScopeErr $ get_implementation_err_msg
        (strlit "static analysis failed to convert in-scope shape")
        ctxt.loc ctxt.scope)
    od ∧
  static_check_exp ctxt (RStruct exps) =
    do
      (* check struct field exps *)
      esret <- static_check_exps ctxt exps;
      (* return exp info with found shape *)
      return <| sh_bd := StructB esret.sh_bds |>
    od ∧
  static_check_exp ctxt (RField index exp) =
    do
      (* check struct exp *)
      eret <- static_check_exp ctxt exp;
      case index_sh_bd index eret.sh_bd of
      | NONE => error (ShapeErr $ concat [
          ctxt.loc; strlit "expression shape "; sh_bd_to_str eret.sh_bd;
          strlit " has no field at index "; num_to_str index;
          strlit " in "; get_scope_desc ctxt.scope; strlit "\n"])
      (* return exp info with found shape *)
      | SOME sb => return <| sh_bd := sb |>
    od ∧
  static_check_exp ctxt (NStruct name eflds) =
    do
      sinfo <-
        case ALOOKUP ctxt.structs name of
        | SOME info => return info
        | NONE => error (ScopeErr $ get_scope_msg Stc ctxt.loc name ctxt.scope);
      (* check struct field exps *)
      (field_names, field_exps) <<- UNZIP eflds;
      esret <- static_check_exps ctxt field_exps;
      field_sbs <<- ZIP (field_names, esret.sh_bds);
      check_struct_fields ctxt name sinfo.fields field_sbs;
      (* return exp info with found shape *)
      return <| sh_bd := NamedB name field_sbs |>
    od ∧
  static_check_exp ctxt (NField field exp) =
    do
      (* check struct exp *)
      eret <- static_check_exp ctxt exp;
      case field_sh_bd field eret.sh_bd of
      | NONE => error (ShapeErr $ concat [
          ctxt.loc; strlit "expression shape "; sh_bd_to_str eret.sh_bd;
          strlit " has no field "; field; strlit " in ";
          get_scope_desc ctxt.scope; strlit "\n"])
      (* return exp info with found shape *)
      | SOME sb => return <| sh_bd := sb |>
    od ∧
  static_check_exp ctxt (Load shape addr) =
    do
      (* check shape *)
      check_shape ctxt.structs ctxt.loc ctxt.scope shape;
      (* check addr exp *)
      aret <- static_check_exp ctxt addr;
      (* check address shape and references base *)
      case aret.sh_bd of
      | StructB _        =>
        error (ShapeErr $ get_non_word_msg
          (strlit "load address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | NamedB _ _       =>
        error (ShapeErr $ get_non_word_msg
          (strlit "load address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | WordB NotBased   =>
        log (WarningErr $ get_memop_msg T T F ctxt.loc ctxt.scope)
      | WordB NotTrusted =>
        log (WarningErr $ get_memop_msg T T T ctxt.loc ctxt.scope)
      | _               => return ();
      case sh_bd_from_sh ctxt.structs Trusted shape of
      (* return exp info *)
      | SOME sb => return <| sh_bd := sb |>
      (* should never occur if static checker implemented correctly *)
      | NONE => error (ScopeErr $ get_implementation_err_msg
        (strlit "static analysis failed to convert in-scope shape")
        ctxt.loc ctxt.scope)
    od ∧
  static_check_exp ctxt (Load32 addr) =
    do
      (* check addr exp *)
      aret <- static_check_exp ctxt addr;
      (* check address shape and references base *)
      case aret.sh_bd of
      | StructB _        =>
        error (ShapeErr $ get_non_word_msg
          (strlit "load address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | NamedB _ _       =>
        error (ShapeErr $ get_non_word_msg
          (strlit "load address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | WordB NotBased   =>
        log (WarningErr $ get_memop_msg T T F ctxt.loc ctxt.scope)
      | WordB NotTrusted =>
        log (WarningErr $ get_memop_msg T T T ctxt.loc ctxt.scope)
      | _               => return ();
      (* return exp info *)
      return <| sh_bd := WordB Trusted |>
    od ∧
  static_check_exp ctxt (LoadByte addr) =
    do
      (* check addr exp *)
      aret <- static_check_exp ctxt addr;
      (* check address shape and references base *)
      case aret.sh_bd of
      | StructB _        =>
        error (ShapeErr $ get_non_word_msg
          (strlit "load address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | NamedB _ _       =>
        error (ShapeErr $ get_non_word_msg
          (strlit "load address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | WordB NotBased   =>
        log (WarningErr $ get_memop_msg T T F ctxt.loc ctxt.scope)
      | WordB NotTrusted =>
        log (WarningErr $ get_memop_msg T T T ctxt.loc ctxt.scope)
      | _               => return ();
      (* return exp info *)
      return <| sh_bd := WordB Trusted |>
    od ∧
  static_check_exp ctxt (Op bop exps) =
    do
      op_str <<- binop_to_str bop;
      (* check num of op args *)
      nargs <<- LENGTH exps;
      case bop of
      | Sub =>
        if ~(nargs = 2) then
          error (GenErr $ get_oparg_msg T (strlit "2") (num_to_str nargs)
            ctxt.loc op_str ctxt.scope)
        else return ()
      | _ =>
        if nargs < 2 then
          error (GenErr $ get_oparg_msg F (strlit "2") (num_to_str nargs)
            ctxt.loc op_str ctxt.scope)
        else return ();
      (* check op args *)
      esret <- static_check_exps ctxt exps;
      (* check arg shapes *)
      b <- check_operands ctxt op_str esret.sh_bds;
      return <| sh_bd := WordB b |>
    od ∧
  static_check_exp ctxt (Panop pop exps) =
    do
      op_str <<- panop_to_str pop;
      (* check num of op args *)
      nargs <<- LENGTH exps;
      case pop of
      | Mul =>
        if ~(nargs = 2) then
          error (GenErr $ get_oparg_msg T (strlit "2") (num_to_str nargs)
            ctxt.loc op_str ctxt.scope)
        else return ();
      (* check op args *)
      esret <- static_check_exps ctxt exps;
      (* check arg shapes *)
      b <- check_operands ctxt op_str esret.sh_bds;
      return <| sh_bd := WordB b |>
    od ∧
  static_check_exp ctxt (Cmp cop exp1 exp2) =
    do
      (* check cmp arg exps *)
      eret1 <- static_check_exp ctxt exp1;
      eret2 <- static_check_exp ctxt exp2;
      (* check for shape match *)
      if ~(sh_bd_eq_shapes eret1.sh_bd eret2.sh_bd) then
        error (ShapeErr $ concat [
            ctxt.loc; strlit "comparison given operands of different shapes in ";
            get_scope_desc ctxt.scope; strlit "\n"])
      else return ();
      (* return exp info *)
      return <| sh_bd := WordB NotBased |>
    od ∧
  static_check_exp ctxt (Shift sop exp n) =
    do
      (* check shifted exp *)
      eret <- static_check_exp ctxt exp;
      (* check exp shape *)
      if ~(sh_bd_has_shape One eret.sh_bd) then
        error (ShapeErr $ get_non_word_msg
          (strlit "shifted expression")
          (sh_bd_to_str eret.sh_bd) ctxt.loc ctxt.scope)
      else return ();
      (* return exp info *)
      return eret
    od ∧
  static_check_exp ctxt BaseAddr =
    (* return exp info *)
    return <| sh_bd := WordB Based |> ∧
  static_check_exp ctxt TopAddr =
    (* return exp info *)
    return <| sh_bd := WordB Based |> ∧
  static_check_exp ctxt BytesInWordB =
    (* return exp info *)
    return <| sh_bd := WordB NotBased |> ∧
  static_check_exps ctxt [] =
    (* return exps info *)
    return <| sh_bds := [] |> ∧
  static_check_exps ctxt (exp::exps) =
    do
      (* check exps *)
      eret <- static_check_exp ctxt exp;
      esret <- static_check_exps ctxt exps;
      (* return exps info with combined basedness and all shapes *)
      return <| sh_bds := eret.sh_bd::esret.sh_bds |>
    od
Termination
  wf_rel_tac `measure (λx. case x of
                           | INL x => exp_size ARB $ SND x
                           | INR x => list_size (exp_size ARB) $ SND x)` >>
  Induct_on ‘eflds’ >- rw[] >>
  Cases >> rw[] >>
  Cases_on ‘UNZIP eflds’ >>
  gvs[] >>
  first_x_assum $ qspec_then `name` assume_tac >>
  intLib.COOPER_TAC
End

(*
  static_check_prog returns:
    (prog info (:prog_return)) static_result
*)
Definition static_check_prog_def:
  static_check_prog ctxt Skip =
    (* return prog info with no checks *)
    return <|
        exits_fun  := F
      ; exits_loop := F
      ; last       := OtherLast
      ; var_delta  := empty mlstring$compare
      ; curr_loc   := ctxt.loc |> ∧
  static_check_prog ctxt (Dec vname shape exp prog) =
    do
      (* check for redeclaration *)
      check_redec_var ctxt vname;
      (* check shape *)
      check_shape ctxt.structs ctxt.loc ctxt.scope shape;
      (* check initialising exp *)
      eret <- static_check_exp ctxt exp;
      (* check for shape match *)
      if ~(sh_bd_has_shape shape eret.sh_bd) then
        error (ShapeErr $ get_shape_mismatch_msg (concat [
            strlit "expression to initialise local variable "; vname
          ]) (sh_bd_to_str eret.sh_bd) (shape_to_str shape)
          ctxt.loc ctxt.scope)
      else return ();
      (* check prog with declared var *)
      ctxt' <<- ctxt with <|
          locals := insert ctxt.locals vname <| vsh_bd := eret.sh_bd |>
        ; last := OtherLast |>;
      pret <- static_check_prog ctxt' prog;
      (* return prog info without declared var *)
      return <|
          exits_fun  := pret.exits_fun
        ; exits_loop := pret.exits_loop
        ; last       := pret.last
        ; var_delta  := delete pret.var_delta vname
        ; curr_loc   := pret.curr_loc |>
    od ∧
  static_check_prog ctxt (DecCall vname shape fname args prog) =
    do
      (* check for redeclaration *)
      check_redec_var ctxt vname;
      (* check shape *)
      check_shape ctxt.structs ctxt.loc ctxt.scope shape;
      (* check func and arg exps *)
      finf <- check_fun_name ctxt fname;
      esret <- static_check_exps ctxt args;
      (* check arg num and shapes *)
      check_func_args ctxt fname finf.params esret.sh_bds;
      (* check for shape match *)
      if ~(shape = finf.ret_shape) then
        error (ShapeErr $ get_shape_mismatch_msg (concat [
            strlit "result of function call "; fname;
            strlit " to initialise local variable "; vname
          ]) (shape_to_str finf.ret_shape) (shape_to_str shape)
          ctxt.loc ctxt.scope)
      else return ();
      (* check prog with declared var *)
      sb <-
        case sh_bd_from_sh ctxt.structs Trusted shape of
        (* return exp info with stored shape *)
        | SOME sb => return sb
        (* should never occur if static checker implemented correctly *)
        | NONE => error (ScopeErr $ get_implementation_err_msg
          (strlit "static analysis failed to convert in-scope shape")
          ctxt.loc ctxt.scope);
      ctxt' <<- ctxt with <|
          locals := insert ctxt.locals vname <| vsh_bd := sb |>
        ; last := OtherLast |>;
      pret <- static_check_prog ctxt' prog;
      (* return prog info without declared var *)
      return <|
          exits_fun  := pret.exits_fun
        ; exits_loop := pret.exits_loop
        ; last       := pret.last
        ; var_delta  := delete pret.var_delta vname
        ; curr_loc   := pret.curr_loc |>
    od ∧
  static_check_prog ctxt (Assign Local vname exp) =
    do
      (* check for out of scope assignment *)
      vinf <- check_local_var ctxt vname;
      (* check assigning exp *)
      eret <- static_check_exp ctxt exp;
      (* check for shape match *)
      if ~(sh_bd_eq_shapes vinf.vsh_bd eret.sh_bd) then
        error (ShapeErr $ get_shape_mismatch_msg (concat [
            strlit "expression assigned to local variable "; vname
          ]) (sh_bd_to_str eret.sh_bd) (sh_bd_to_str vinf.vsh_bd)
          ctxt.loc ctxt.scope)
      else return ();
      (* return prog info with updated var *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  :=
          singleton mlstring$compare vname (vinf with
            <| vsh_bd := eret.sh_bd |>)
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Assign Global vname exp) =
    do
      (* check for out of scope assignment *)
      vinf <- check_global_var ctxt vname;
      (* check assigning exp *)
      eret <- static_check_exp ctxt exp;
      (* check for shape match *)
      if ~(sh_bd_has_shape vinf.vshape eret.sh_bd) then
        error (ShapeErr $ get_shape_mismatch_msg (concat [
            strlit "expression assigned to global variable "; vname
          ]) (sh_bd_to_str eret.sh_bd) (shape_to_str vinf.vshape)
          ctxt.loc ctxt.scope)
      else return ();
      (* return prog info with updated var *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Primitive v pop es) =
    do
      (* check destination is in scope (Primitive always targets Local) *)
      vinf <- check_local_var ctxt v;
      (* check arg exps *)
      esret <- static_check_exps ctxt es;
      (* per-primop arity/operand checks; returns result shaped basedness *)
      res_sb <- case pop of
                | AddCarry => check_addcarry_args ctxt esret.sh_bds;
      (* check declared destination shape matches result shape *)
      if ~(sh_bd_eq_shapes vinf.vsh_bd res_sb)
        then error (ShapeErr $ get_shape_mismatch_msg (concat [
            «result of primitive »; primop_to_str pop;
            « assigned to local variable »; v
          ]) (sh_bd_to_str res_sb) (sh_bd_to_str vinf.vsh_bd)
          ctxt.loc ctxt.scope)
      else return ();
      (* return prog info with updated var *)
      return <| exits_fun  := F
              ; exits_loop := F
              ; last       := OtherLast
              ; var_delta  := singleton mlstring$compare v
                                (vinf with <| vsh_bd := res_sb |>)
              ; curr_loc   := ctxt.loc |>
    od ∧
      static_check_prog ctxt (AssignCall (Local, vname) hdl fname args) =
    do
      (* check for out of scope assignment *)
      vinf <- check_local_var ctxt vname;
      (* check func ptr exp and arg exps *)
      finf <- check_fun_name ctxt fname;
      esret <- static_check_exps ctxt args;
      (* check arg num and shapes *)
      check_func_args ctxt fname finf.params esret.sh_bds;
      (* check for shape match *)
      if ~(sh_bd_has_shape finf.ret_shape vinf.vsh_bd) then
        error (ShapeErr $ get_shape_mismatch_msg (concat [
            strlit "result of function call "; fname;
            strlit " assigned to local variable "; vname
          ]) (shape_to_str finf.ret_shape) (sh_bd_to_str vinf.vsh_bd)
          ctxt.loc ctxt.scope)
      else return ();
      (* check exception handling info *)
      case hdl of
      | NONE => return ()
        (* check for out of scope exception variable *)
      | SOME (eid, evar, prog) =>
          do
            evinf <- check_local_var ctxt evar;
            static_check_prog (ctxt with locals :=
                insert ctxt.locals evar (evinf with
                  <| vsh_bd := sh_bd_from_bd Trusted evinf.vsh_bd |>
              )) prog;
            return ()
          od;
      (* return prog info with updated var *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  :=
          singleton mlstring$compare vname (vinf with
            <| vsh_bd := sh_bd_from_bd Trusted vinf.vsh_bd |>)
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (AssignCall (Global, vname) hdl fname args) =
    do
      (* check for out of scope assignment *)
      vinf <- check_global_var ctxt vname;
      (* check func ptr exp and arg exps *)
      finf <- check_fun_name ctxt fname;
      esret <- static_check_exps ctxt args;
      (* check arg num and shapes *)
      check_func_args ctxt fname finf.params esret.sh_bds;
      (* check for shape match *)
      if ~(vinf.vshape = finf.ret_shape) then
        error (ShapeErr $ get_shape_mismatch_msg (concat [
            strlit "result of function call "; fname;
            strlit " assigned to global variable "; vname
          ]) (shape_to_str finf.ret_shape) (shape_to_str vinf.vshape)
          ctxt.loc ctxt.scope)
      else return ();
      (* check exception handling info *)
      case hdl of
      | NONE => return ()
        (* check for out of scope exception variable *)
      | SOME (eid, evar, prog) =>
          do
            evinf <- check_local_var ctxt evar;
            static_check_prog (ctxt with locals :=
                insert ctxt.locals evar (evinf with
                  <| vsh_bd := sh_bd_from_bd Trusted evinf.vsh_bd |>
              )) prog;
            return ()
          od;
      (* return prog info with updated var *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Return exp) =
    do
      (* check return value exp *)
      eret <- static_check_exp ctxt exp;
      (* lookup current function info *)
      finf <-
        case ctxt.scope of
        | FunScope fname _ => check_fun_name ctxt fname
        (* should never occur if static checker implemented correctly *)
        | _ => error (GenErr $ get_implementation_err_msg
          (strlit "return found outside function scope")
          ctxt.loc ctxt.scope);
      (* check for shape match *)
      if ~(sh_bd_has_shape finf.ret_shape eret.sh_bd) then
        error (ShapeErr $ get_shape_mismatch_msg
          (strlit "expression to return")
          (sh_bd_to_str eret.sh_bd) (shape_to_str finf.ret_shape)
          ctxt.loc ctxt.scope)
      else return ();
      (* return prog info *)
      return <|
          exits_fun  := T
        ; exits_loop := F
        ; last       := RetLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (TailCall fname args) =
    do
      (* lookup current function info *)
      caller_inf <- case ctxt.scope of
        | FunScope caller _ => check_fun_name ctxt caller
        (* should never occur if static checker implemented correctly *)
        | _ => error (GenErr $ strlit "tail call found outside function scope");
      (* check func ptr exp and arg exps *)
      callee_inf <- check_fun_name ctxt fname;
      esret <- static_check_exps ctxt args;
      (* check for shape match *)
      if ~(caller_inf.ret_shape = callee_inf.ret_shape) then
        error (ShapeErr $ get_shape_mismatch_msg (concat [
            strlit "result of function call "; fname;
            strlit " to return"
          ]) (shape_to_str callee_inf.ret_shape)
          (shape_to_str caller_inf.ret_shape)
          ctxt.loc ctxt.scope)
      else return ();
      (* check arg num and shapes *)
      check_func_args ctxt fname callee_inf.params esret.sh_bds;
      (* return prog info *)
      return <|
          exits_fun  := T
        ; exits_loop := F
        ; last       := TailLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (StandAloneCall hdl fname args) =
    do
      (* check func ptr exp and arg exps *)
      finf <- check_fun_name ctxt fname;
      esret <- static_check_exps ctxt args;
      (* check arg num and shapes *)
      check_func_args ctxt fname finf.params esret.sh_bds;
      (* check exception handling info *)
      case hdl of
      | NONE => return ()
        (* check for out of scope exception variable *)
      | SOME (eid, evar, prog) =>
          do
            evinf <- check_local_var ctxt evar;
            static_check_prog (ctxt with locals :=
                insert ctxt.locals evar (evinf with
                  <| vsh_bd := sh_bd_from_bd Trusted evinf.vsh_bd |>
              )) prog;
            return ()
          od;
      (* return prog info *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (ExtCall fname ptr1 len1 ptr2 len2) =
    do
      (* check arg exps *)
      esret <- static_check_exps ctxt [ptr1;len1;ptr2;len2];
      (* check arg shapes *)
      case FIND (\sb. ~(sh_bd_has_shape One sb)) esret.sh_bds of
      | SOME sb => error (ShapeErr $ get_non_word_msg (concat [
          strlit "value for argument given to FFI "; fname
        ]) (sh_bd_to_str sb) ctxt.loc ctxt.scope)
      | NONE => return ();
      (* return prog info *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Seq prog1 prog2) =
    do
      (* check for prior warnable unreachability *)
      (warn_p1, ctxt1) <<- reached_warnable prog1 ctxt;
      case warn_p1 of
      | SOME ls =>
        log (WarningErr $ get_unreach_msg ctxt1.loc (last_to_str ls) ctxt1.scope)
      | NONE   => return ();
      (* check first prog *)
      pret1 <- static_check_prog ctxt1 prog1;
      (* update unreachability after first prog *)
      next_r <<- next_is_reachable ctxt1.is_reachable pret1.last;
      ctxt2 <<- ctxt1 with <|
          locals := seq_loc_inf ctxt1.locals pret1.var_delta
        ; is_reachable := next_r
        ; last :=
          if next_now_unreachable ctxt1.is_reachable next_r then pret1.last
          else ctxt1.last
        ; loc := pret1.curr_loc |>;
      (* check for warnable unreachability after first prog *)
      (warn_p2, ctxt3) <<- reached_warnable prog2 ctxt2;
      case warn_p2 of
      | SOME ls =>
        log (WarningErr $ get_unreach_msg ctxt3.loc (last_to_str ls) ctxt1.scope)
      | NONE   => return ();
      (* check second prog *)
      pret2 <- static_check_prog ctxt3 prog2;
      (* return prog info by combining both appropriately *)
      return <|
          exits_fun  := (pret1.exits_fun \/ pret2.exits_fun)
        ; exits_loop := (pret1.exits_loop \/ pret2.exits_loop)
        ; last       := seq_last_stmt pret1.last pret2.last
        ; var_delta  := seq_loc_inf pret1.var_delta pret2.var_delta
        ; curr_loc   := pret2.curr_loc |>
    od ∧
  static_check_prog ctxt (If exp prog1 prog2) =
    do
      (* check condition exp *)
      eret <- static_check_exp ctxt exp;
      (* check condition shape *)
      if ~(sh_bd_has_shape One eret.sh_bd) then
        error (ShapeErr $ get_non_word_msg
          (strlit "if condition") (sh_bd_to_str eret.sh_bd) ctxt.loc ctxt.scope)
      else return ();
      (* check branches *)
      pret1 <- static_check_prog ctxt prog1;
      pret2 <- static_check_prog (ctxt with loc := pret1.curr_loc) prog2;
      (* return prog info by combining both appropriately *)
      double_ret <<- (pret1.exits_fun /\ pret2.exits_fun);
      double_loop_exit <<- (pret1.exits_loop /\ pret2.exits_loop);
      return <|
          exits_fun  := double_ret
        ; exits_loop := double_loop_exit
        ; last       := branch_last_stmt double_ret double_loop_exit
        ; var_delta  := branch_loc_inf ctxt.locals pret1.var_delta pret2.var_delta
        ; curr_loc   := pret2.curr_loc |>
    od ∧
  static_check_prog ctxt (While exp prog) =
    do
      (* check condition exp *)
      eret <- static_check_exp ctxt exp;
      (* check condition shape *)
      if ~(sh_bd_has_shape One eret.sh_bd) then
        error (ShapeErr $ get_non_word_msg
          (strlit "while condition") (sh_bd_to_str eret.sh_bd) ctxt.loc ctxt.scope)
      else return ();
      (* check loop body *)
      pret <- static_check_prog (ctxt with in_loop := T) prog;
      (* return prog info by treating like an else-less If *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  :=
            branch_loc_inf ctxt.locals pret.var_delta $ mlmap$empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt Break =
    do
      (* check for rogueness *)
      if ~ctxt.in_loop then
        error (GenErr $ get_rogue_msg T ctxt.loc ctxt.scope)
      else return ();
      (* return prog info *)
      return <|
          exits_fun  := F
        ; exits_loop := T
        ; last       := BreakLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt Continue =
    do
      (* check for rogueness *)
      if ~ctxt.in_loop then
        error (GenErr $ get_rogue_msg F ctxt.loc ctxt.scope)
      else return ();
      (* return prog info *)
      return <|
          exits_fun  := F
        ; exits_loop := T
        ; last       := ContLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Raise eid exp) =
    do
      (* check exception value exp *)
      static_check_exp ctxt exp;
      (* return prog info *)
      return <|
          exits_fun  := T
        ; exits_loop := F
        ; last       := RaiseLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Store addr exp) =
    do
      (* check address and value exps *)
      aret <- static_check_exp ctxt addr;
      eret <- static_check_exp ctxt exp;
      (* check address shape and references base *)
      case aret.sh_bd of
      | StructB _        =>
        error (ShapeErr $ get_non_word_msg
          (strlit "store address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | NamedB _ _       =>
        error (ShapeErr $ get_non_word_msg
          (strlit "store address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | WordB NotBased   =>
        log (WarningErr $ get_memop_msg T F F ctxt.loc ctxt.scope)
      | WordB NotTrusted =>
        log (WarningErr $ get_memop_msg T F T ctxt.loc ctxt.scope)
      | _               => return ();
      (* return prog info *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (Store32 addr exp) =
    do
      (* check address and value exps *)
      aret <- static_check_exp ctxt addr;
      eret <- static_check_exp ctxt exp;
      (* check address shape and references base *)
      case aret.sh_bd of
      | StructB _        =>
        error (ShapeErr $ get_non_word_msg
          (strlit "store address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | NamedB _ _       =>
        error (ShapeErr $ get_non_word_msg
          (strlit "store address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | WordB NotBased   =>
        log (WarningErr $ get_memop_msg T F F ctxt.loc ctxt.scope)
      | WordB NotTrusted =>
        log (WarningErr $ get_memop_msg T F T ctxt.loc ctxt.scope)
      | _               => return ();
      (* check value shape *)
      if ~(sh_bd_has_shape One eret.sh_bd) then
        error (ShapeErr $ get_non_word_msg
          (strlit "store value") (sh_bd_to_str eret.sh_bd) ctxt.loc ctxt.scope)
      else return ();
      (* return prog info *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (StoreByte addr exp) =
    do
      (* check address and value exps *)
      aret <- static_check_exp ctxt addr;
      eret <- static_check_exp ctxt exp;
      (* check address shape and references base *)
      case aret.sh_bd of
      | StructB _        =>
        error (ShapeErr $ get_non_word_msg
          (strlit "store address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | NamedB _ _       =>
        error (ShapeErr $ get_non_word_msg
          (strlit "store address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | WordB NotBased   =>
        log (WarningErr $ get_memop_msg T F F ctxt.loc ctxt.scope)
      | WordB NotTrusted =>
        log (WarningErr $ get_memop_msg T F T ctxt.loc ctxt.scope)
      | _               => return ();
      (* check value shape *)
      if ~(sh_bd_has_shape One eret.sh_bd) then
        error (ShapeErr $ get_non_word_msg
          (strlit "store value") (sh_bd_to_str eret.sh_bd) ctxt.loc ctxt.scope)
      else return ();
      (* return prog info *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (ShMemLoad mop Local vname addr) =
    do
      (* check for out of scope var *)
      vinf <- check_local_var ctxt vname;
      (* check address exp *)
      aret <- static_check_exp ctxt addr;
      (* check address shape and references base *)
      case aret.sh_bd of
      | StructB _        =>
        error (ShapeErr $ get_non_word_msg
          (strlit "load address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | NamedB _ _       =>
        error (ShapeErr $ get_non_word_msg
          (strlit "load address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | WordB Based      =>
        log (WarningErr $ get_memop_msg F T F ctxt.loc ctxt.scope)
      | WordB NotTrusted =>
        log (WarningErr $ get_memop_msg F T T ctxt.loc ctxt.scope)
      | _               => return ();
      (* check value shape *)
      if ~(sh_bd_has_shape One vinf.vsh_bd) then
        error (ShapeErr $ get_non_word_msg
          (strlit "load variable") (sh_bd_to_str vinf.vsh_bd) ctxt.loc ctxt.scope)
      else return ();
      (* return prog info with updated var *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  :=
          singleton mlstring$compare vname (vinf with
            <| vsh_bd := sh_bd_from_bd Trusted vinf.vsh_bd |>)
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (ShMemLoad mop Global vname addr) =
    do
      (* check for out of scope var *)
      vinf <- check_global_var ctxt vname;
      (* check address exp *)
      aret <- static_check_exp ctxt addr;
      (* check address shape and references base *)
      case aret.sh_bd of
      | StructB _        =>
        error (ShapeErr $ get_non_word_msg
          (strlit "load address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | NamedB _ _       =>
        error (ShapeErr $ get_non_word_msg
          (strlit "load address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | WordB Based      =>
        log (WarningErr $ get_memop_msg F T F ctxt.loc ctxt.scope)
      | WordB NotTrusted =>
        log (WarningErr $ get_memop_msg F T T ctxt.loc ctxt.scope)
      | _               => return ();
      (* check value shape *)
      if ~(One = vinf.vshape) then
        error (ShapeErr $ get_non_word_msg
          (strlit "load variable") (shape_to_str vinf.vshape) ctxt.loc ctxt.scope)
      else return ();
      (* return prog info with updated var *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt (ShMemStore mop addr exp) =
    do
      (* check address and value exps *)
      aret <- static_check_exp ctxt addr;
      eret <- static_check_exp ctxt exp;
      (* check address shape and references base *)
      case aret.sh_bd of
      | StructB _        =>
        error (ShapeErr $ get_non_word_msg
          (strlit "store address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | NamedB _ _       =>
        error (ShapeErr $ get_non_word_msg
          (strlit "store address") (sh_bd_to_str aret.sh_bd) ctxt.loc ctxt.scope)
      | WordB Based      =>
        log (WarningErr $ get_memop_msg F F F ctxt.loc ctxt.scope)
      | WordB NotTrusted =>
        log (WarningErr $ get_memop_msg F F T ctxt.loc ctxt.scope)
      | _               => return ();
      (* check value shape *)
      if ~(sh_bd_has_shape One eret.sh_bd) then
        error (ShapeErr $ get_non_word_msg
          (strlit "store value") (sh_bd_to_str eret.sh_bd) ctxt.loc ctxt.scope)
      else return ();
      (* return prog info *)
      return <|
          exits_fun  := F
        ; exits_loop := F
        ; last       := OtherLast
        ; var_delta  := empty mlstring$compare
        ; curr_loc   := ctxt.loc |>
    od ∧
  static_check_prog ctxt Tick =
    (* return prog info with no checks *)
    return <|
        exits_fun  := F
      ; exits_loop := F
      ; last       := InvisLast
      ; var_delta  := empty mlstring$compare
      ; curr_loc   := ctxt.loc |> ∧
  static_check_prog ctxt (Annot tag str) =
    (* update current location *)
    let loc =
      if (tag = «location») then
        concat [strlit "AT "; str; strlit ": "]
      else ctxt.loc in
    (* return prog info with no checks *)
    return <|
        exits_fun  := F
      ; exits_loop := F
      ; last       := InvisLast
      ; var_delta  := empty mlstring$compare
      ; curr_loc   := loc |>
End

(*
  static_check_progs returns:
    (unit) static_result
*)
Definition static_check_progs_def:
  static_check_progs fctxt gctxt sctxt [] =
    (* no more decls *)
    return () ∧
  static_check_progs fctxt gctxt sctxt (Name _ _::decls) =
    (* not a function *)
    static_check_progs fctxt gctxt sctxt decls ∧
  static_check_progs fctxt gctxt sctxt (Decl _ _ _::decls) =
    (* not a function *)
    static_check_progs fctxt gctxt sctxt decls ∧
  static_check_progs fctxt gctxt sctxt (Function fi::decls) =
    do
      (param_names, param_shapes) <<- UNZIP fi.params;
      param_sbs <-
        case OPT_MMAP (sh_bd_from_sh sctxt Trusted) param_shapes of
        (* return exp info with stored shape *)
        | SOME sbs => return $ ZIP (param_names, sbs)
        (* should never occur if static checker implemented correctly *)
        | NONE => error (ScopeErr $ get_implementation_err_msg
          (strlit "static analysis failed to convert in-scope shape")
          (strlit "") (FunScope fi.name (strlit "")));
      (* setup initial checking context *)
      ctxt <<- <| locals :=
                  FOLDL (\m (v,sb). insert m v <| vsh_bd := sb |>)
                    (empty mlstring$compare) param_sbs
                ; globals := gctxt
                ; funcs := fctxt
                ; structs := sctxt
                ; scope := FunScope fi.name (strlit "")
                ; in_loop := F
                ; is_reachable := IsReach
                ; last := InvisLast
                ; loc := «» |>;
      (* check function body *)
      prog_ret <- static_check_prog ctxt fi.body;
      (* check missing function exit *)
      if ~(prog_ret.exits_fun) then
        error (GenErr $ concat [
            strlit "branches missing return statement in ";
            get_scope_desc (FunScope fi.name (strlit "")); strlit "\n"])
      else return ();
      (* check remaining functions *)
      static_check_progs fctxt gctxt sctxt decls
    od
End

(*
  static_check_decls returns:
    ((varname, global_info) map, (funname, func_info) map) static_result
*)
Definition static_check_decls_def:
  static_check_decls fctxt gctxt sctxt [] =
    (* no more decls *)
    return (fctxt, gctxt) ∧
  static_check_decls fctxt gctxt sctxt (Name _ _::decls) =
    (* already processed *)
    static_check_decls fctxt gctxt sctxt decls ∧
  static_check_decls fctxt gctxt sctxt (Decl shape vname exp::decls) =
    do
      (* setup initial checking context *)
      ctxt <<- <| locals := empty mlstring$compare
                ; globals := gctxt
                ; funcs := empty mlstring$compare
                ; structs := sctxt
                ; scope := DeclScope vname
                ; in_loop := F
                ; is_reachable := IsReach
                ; last := InvisLast
                ; loc := «» |>;
      (* check for redeclaration *)
      check_redec_var (ctxt with scope := TopLevel) vname;
      (* check shape *) (* TODO: decl locs*)
      check_shape sctxt (strlit "") ctxt.scope shape;
      (* check initialisation expression *)
      eret <- static_check_exp ctxt exp;
      (* check for shape match *)
      if ~(sh_bd_has_shape shape eret.sh_bd) then
        error (ShapeErr $ get_shape_mismatch_msg (concat [
            strlit "expression to initialise global variable "; vname
          ]) (sh_bd_to_str eret.sh_bd) (shape_to_str shape)
          (strlit "") ctxt.scope)
      else return ();
      (* check remaining decls *)
      static_check_decls fctxt (insert gctxt vname
          <| vshape := shape |>
        ) sctxt decls
    od ∧
  static_check_decls fctxt gctxt sctxt (Function fi::decls) =
    do
      (* check for redeclaration *) (* TODO: decl locs *)
      if member fi.name fctxt then
        error (ScopeErr $ get_redec_msg Fun (strlit "") fi.name TopLevel)
      else return ();
      (* check main func *)
      if fi.name = «main» then
        do
          (* check main func args *)
          if LENGTH fi.params > 0 then
            error (GenErr $ strlit "main function has arguments\n")
          else return ();
          (* check main func export status *)
          if fi.export then
            error (GenErr $ strlit "main function is exported\n")
          else return ();
          (* check main func return shape *)
          if ~(fi.return = One) then
            error (ShapeErr $ get_non_word_msg
              (strlit "main function return") (shape_to_str fi.return)
              (strlit "") (FunScope fi.name (strlit "")))
          else return ();
        od
      else
        do
          (* check arg name uniqueness *)
          case first_repeat $ sort mlstring_lt (MAP FST fi.params) of
            SOME pname => error (ScopeErr $ concat [
                strlit "parameter "; pname; strlit " is redeclared in function ";
                fi.name; strlit "\n"])
          | NONE => return ();
          (* check exported func *)
          if fi.export then
            do
              (* check exported func arg num *)
              if LENGTH fi.params > 4 then
                error (GenErr $ concat [
                    strlit "exported function "; fi.name;
                    strlit " has more than 4 arguments\n"])
              else return ();
              (* check exported func arg shape *)
              check_export_params (strlit "")
                (FunScope fi.name (strlit "")) fi.params;
              (* check exported func return shape *)
              if ~(fi.return = One) then
                error (ShapeErr $ get_non_word_msg
                  (strlit "exported function return") (shape_to_str fi.return)
                  (strlit "") (FunScope fi.name (strlit "")))
              else return ();
            od
          else
            (* check arg shapes *) (* TODO: decl locs*)
            check_id_shapes sctxt (strlit "")
              (FunScope fi.name (strlit "")) fi.params;
            (* check return shape *)
            check_shape sctxt (strlit "")
              (FunScope fi.name (strlit " return")) fi.return;
            (* check func return shape size *)
            if size_of_sh_with_ctxt sctxt fi.return > 32 then
              error (ShapeErr $ concat [
                  strlit "function "; fi.name;
                  strlit " returns a shape bigger than 32 words\n"])
            else return () ;
        od ;
      (* check remaining decls *)
      static_check_decls (insert fctxt fi.name
          <| ret_shape := fi.return ; params := fi.params |>
        ) gctxt sctxt decls
    od
End

(*
  static_check_names returns:
    ((stcname # struct_info) list) static_result
*)
Definition static_check_names_def:
  static_check_names sctxt [] =
    (* no more decls *)
    return sctxt ∧
  static_check_names sctxt (Name name flds::decls) =
    do
      (* check for redeclaration *)
      case ALOOKUP sctxt name of
      | SOME info =>
        error (ScopeErr $ get_redec_msg Stc (strlit "") name TopLevel)
      | NONE => return ();
      (* check field name uniqueness *)
      case first_repeat $ sort mlstring_lt (MAP FST flds) of
        SOME fld => error (ScopeErr $ concat [
            strlit "field "; fld; strlit " is redeclared in struct name ";
            name; strlit "\n"])
      | NONE => return ();
      (* check field shapes *) (* TODO: decl locs *)
      check_id_shapes sctxt (strlit "") (StcScope name (strlit "")) flds;
      (* setup struct info *)
      info <<- <| fields := flds
                ; size := size_of_sh_with_ctxt sctxt (Comb $ MAP SND flds) |>;
      (* check remaining names *)
      static_check_names ((name,info)::sctxt) decls
    od ∧
  static_check_names sctxt (_::decls) =
    (* not a struct name *)
    static_check_names sctxt decls
End

(*
  static_check returns:
    (unit) static_result

  The static checker returns () if no error occurred, or the static error
  encountered, along with a list of warnings encountered (if any). All warnings
  and errors come with a message containing the issue and its location
*)
Definition static_check_def:
  static_check decls =
    do
      (* check decls and build context *)
      sctxt <- static_check_names [] decls;
      (fctxt, gctxt) <-
        static_check_decls (empty mlstring$compare)
        (empty mlstring$compare) sctxt decls;
      (* check function bodies with context *)
      static_check_progs fctxt gctxt sctxt decls
    od
End
