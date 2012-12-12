structure ml_translatorLib :> ml_translatorLib =
struct

open HolKernel boolLib bossLib;

open MiniMLTheory MiniMLTerminationTheory;
open Print_astTheory Print_astTerminationTheory intLib;
open ml_translatorTheory;
open arithmeticTheory listTheory combinTheory pairTheory;
open integerTheory intLib ml_optimiseTheory;

infix \\ val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* packers and unpackers for thms, terms and types *)

fun pack_type ty = REFL (mk_var("ty",ty));
fun unpack_type th = th |> concl |> dest_eq |> fst |> type_of;

fun pack_term tm = REFL tm;
fun unpack_term th = th |> concl |> dest_eq |> fst;

fun pack_thm th = PURE_ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def] th |> DISCH_ALL;
fun unpack_thm th = th |> UNDISCH_ALL |> PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def];

fun pack_string s = REFL (mk_var(s,``:bool``))
fun unpack_string th = th |> concl |> dest_eq |> fst |> dest_var |> fst

fun pack_list f xs = TRUTH :: map f xs |> LIST_CONJ |> PURE_ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def];
fun unpack_list f th = th |> PURE_ONCE_REWRITE_RULE [markerTheory.Abbrev_def] |> CONJUNCTS |> tl |> map f;

fun pack_pair f1 f2 (x1,x2) = pack_list I [f1 x1, f2 x2]
fun unpack_pair f1 f2 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x)) end

fun pack_triple f1 f2 f3 (x1,x2,x3) = pack_list I [f1 x1, f2 x2, f3 x3]
fun unpack_triple f1 f2 f3 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x), f3 (el 3 x)) end

fun pack_4tuple f1 f2 f3 f4 (x1,x2,x3,x4) = pack_list I [f1 x1, f2 x2, f3 x3, f4 x4]
fun unpack_4tuple f1 f2 f3 f4 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x), f3 (el 3 x), f4 (el 4 x)) end

fun pack_5tuple f1 f2 f3 f4 f5 (x1,x2,x3,x4,x5) = pack_list I [f1 x1, f2 x2, f3 x3, f4 x4, f5 x5]
fun unpack_5tuple f1 f2 f3 f4 f5 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x), f3 (el 3 x), f4 (el 4 x), f5 (el 5 x)) end


exception UnableToTranslate of term;
exception UnsupportedType of hol_type;

(* code for managing state of certificate theorems *)

local
  (* inv: get_DeclAssum () is a hyp in each thm in each !cert_memory *)
  val module_name = ref "";
  val decl_abbrev = ref TRUTH;
  val decl_term   = ref ``[]:dec list``;
  val cert_memory = ref ([] : (string * term * thm * thm) list);
  (* session specific state below *)
  val abbrev_counter = ref 0;
  val abbrev_defs = ref ([]:thm list);
in
  fun cert_reset () =
    (module_name := "";
     decl_abbrev := TRUTH;
     decl_term   := ``[]:dec list``;
     cert_memory := [];
     (* abbrev_counter := 0; *)
     abbrev_defs := [])
  fun map_cert_memory f = (cert_memory := map f (!cert_memory))
  fun get_names () = map (fn (n,_,_,_) => n) (!cert_memory)
  fun get_module_name () = let
     val n = !module_name
     in if n <> "" then n else
          let val c = current_theory() in (module_name := c; c) end end
  fun get_DeclAssum () = ``DeclAssum ^(!decl_term) env``
  fun get_decls () = let
    val rw = !decl_abbrev
    val tm = QCONV (REWRITE_CONV [rw]) (!decl_term) |> concl |> rand
    in tm end
  fun get_decl_abbrev () = let
    val abbrev = !decl_abbrev
    in if concl abbrev = T then NONE else SOME abbrev end;
  (* decl abbreviation *)
  fun update_decl_abbreviation () = let
    val rhs = (!decl_term)
    val name = get_module_name () ^ "_decls_" ^ int_to_string (!abbrev_counter)
    val _ = (abbrev_counter := 1 + (!abbrev_counter))
    val abbrev_def = new_definition(name,mk_eq(mk_var(name,``:decs``),rhs))
    val new_rw = REWRITE_RULE [abbrev_def |> GSYM]
    val _ = map_cert_memory (fn (n,tm,th,pre) => (n,tm,new_rw th,pre))
    val _ = (decl_term := (abbrev_def |> concl |> dest_eq |> fst))
    val _ = (abbrev_defs := abbrev_def::(!abbrev_defs))
    in () end
  fun finish_decl_abbreviation () = let
    val tm = (!decl_term)
    val lemma = tm |> QCONV (REWRITE_CONV (SNOC::(!abbrev_defs)))
    val rhs = lemma |> concl |> rand
    val name = get_module_name () ^ "_decls"
    val abbrev_def = new_definition(name,mk_eq(mk_var(name,``:decs``),rhs))
    val new_rw = REWRITE_RULE [lemma |> RW [GSYM abbrev_def]]
    val _ = map_cert_memory (fn (n,tm,th,pre) => (n,tm,new_rw th,pre))
    val _ = (decl_term := (abbrev_def |> concl |> dest_eq |> fst))
    val _ = (decl_abbrev := abbrev_def)
    val strs = (!abbrev_defs) |> map (fst o dest_const o fst o dest_eq o concl)
    val _ = map (fn s => delete_const s handle NotFound => ()) strs
    in () end;
  (* functions for appending a new declaration *)
  fun snoc_decl decl = let
    val _ = (decl_term := listSyntax.mk_snoc(decl,!decl_term))
    val f = if can (match_term ``Dletrec funs``) decl then
              (fn (n:string,tm:term,th,pre) =>
                (n,tm,(MATCH_MP DeclAssum_Dletrec th |> SPEC (rand decl)
                 |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) |> REWRITE_RULE [])
                 handle HOL_ERR _ => th,pre))
            else if can (match_term ``Dlet v x``) decl then
              (fn (n:string,tm:term,th,pre) =>
                (n,tm,(MATCH_MP DeclAssum_Dlet th
                 |> SPEC (rand (rand (rator decl))) |> SPEC (rand decl)
                 |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) |> REWRITE_RULE [])
                 handle HOL_ERR _ => th,pre))
            else if can (match_term ``Dtype x``) decl then
              (fn (n:string,tm:term,th,pre) =>
                (n,tm,(MATCH_MP DeclAssum_Dtype th |> SPEC (rand decl))
                      handle HOL_ERR _ => th,pre))
            else fail()
    val _ = map_cert_memory f
    in () end;
  fun snoc_dtype_decl dtype = let
    val decl = dtype
    val _ = snoc_decl decl
    val _ = update_decl_abbreviation ()
    in () end
  (* storing and looking up certificate theorems *)
  fun store_eval_thm th = let
    val th = if mem (get_DeclAssum ()) (hyp th) then DISCH (get_DeclAssum ()) th |> Q.GEN `env` else th
    val tm = concl (th |> SPEC_ALL |> UNDISCH_ALL)
    val const = tm |> rand |> rand
    val n = term_to_string const
    val _ = (cert_memory := (n,const,th,TRUTH)::(!cert_memory))
    in th end;
  fun store_cert th pre = let
    val decl_assum = (th |> hyp |> first (can (match_term ``DeclAssum ds env``)))
    val th = Q.GEN `env` (DISCH decl_assum th)
    val decl = (decl_assum |> rator |> rand |> rator |> rand)
    val _ = snoc_decl decl
    val tm = concl (th |> SPEC_ALL |> UNDISCH_ALL)
    val const = tm |> rand |> rand
    val _ = is_const const orelse fail()
    val n = tm |> rator |> rand |> rand |> stringSyntax.fromHOLstring
    val _ = (cert_memory := (n,const,th,pre)::(!cert_memory))
    val _ = update_decl_abbreviation ()
    val (_,_,th,pre) = hd (!cert_memory)
    in th end
  fun lookup_cert const = let
    val (name,c,th,pre) = (first (fn (_,c,_,_) => can (match_term c) const) (!cert_memory))
    val th = th |> SPEC_ALL |> UNDISCH_ALL
    val th = MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] Eval_Var_SWAP_ENV)
                      (th |> Q.INST [`env`|->`shaddow_env`]) |> UNDISCH_ALL
             handle HOL_ERR _ => th
    in th end
  fun get_cert fname = let
    val (name,c,th,pre) = (first (fn (n,_,_,_) => n = fname) (!cert_memory))
    in (th |> SPEC_ALL |> UNDISCH_ALL, pre) end
  (* simplifying side conditions in certificate theorems *)
  fun update_precondition new_pre = let
    fun get_const def = def |> SPEC_ALL |> CONJUNCTS |> hd
                            |> concl |> dest_eq |> fst |> repeat rator
    val pre_const = get_const new_pre
    val (fname,c,th,pre) = (first (fn (_,_,_,pre) => can (find_term (can (match_term pre_const))) (get_const pre) handle HOL_ERR _ => false) (!cert_memory))
    val pre_is_single_line =
      (length (new_pre |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL) = 1)
    val pre_is_true = let val p = new_pre |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL
                          val rhs = hd p |> concl |> dest_eq |> snd
                      in (rhs = T) andalso (length p = 1) end
    val pre_is_rec = let val rhss = new_pre |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL
                                            |> map (snd o dest_eq o concl o SPEC_ALL)
                     in 0 < length (filter (can (find_term (can (match_term pre_const)))) rhss) end
    val (th1,pre1) =
      if pre_is_true then let
        val th = th |> DISCH_ALL |> RW [new_pre,PRECONDITION_def] |> UNDISCH_ALL
                    |> Q.SPEC `env` |> UNDISCH_ALL
        val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
        val vs = find_terms (can (match_term pat)) (concl th) |> map rand
        val th = GENL vs th |> SIMP_RULE std_ss [FUN_QUANT_SIMP,Eval_FUN_FORALL_EQ]
        val th = DISCH (get_DeclAssum ()) th |> Q.GEN `env`
        in (th,TRUTH) end else
      if pre_is_rec orelse not pre_is_single_line then (th,new_pre) else
        (DISCH_ALL th |> RW1 [new_pre] |> UNDISCH_ALL, TRUTH)
    val _ = map_cert_memory (fn (f,x,th,pre) =>
              if f = fname then (fname,c,th1,pre1) else (f,x,th,pre))
    in new_pre end
  (* store/load to/from a single thm *)
  fun pack_certs () = let
    val _ = finish_decl_abbreviation ()
    in pack_triple
         (pack_list (pack_4tuple pack_string pack_term pack_thm pack_thm))
         pack_thm pack_term
           ((!cert_memory), (!decl_abbrev), (!decl_term)) end
  fun unpack_certs th = let
    val (cert,abbrev,t) =
      unpack_triple
        (unpack_list (unpack_4tuple unpack_string unpack_term unpack_thm unpack_thm))
        unpack_thm unpack_term th
    val _ = (cert_memory := cert)
    val _ = (decl_abbrev := abbrev)
    val _ = (abbrev_defs := [abbrev])
    val _ = (decl_term := t)
    in () end
end


(* code for managing type information *)

local
  val type_mappings = ref ([]:(hol_type * hol_type) list)
  val other_types = ref ([]:(hol_type * term) list)
  val preprocessor_rws = ref ([]:thm list)
  val type_memory = ref ([]:(hol_type * thm * (term * thm) list * thm) list)
  val all_eq_lemmas = ref (CONJUNCTS EqualityType_NUM_BOOL)
in
  fun type_reset () =
    (type_mappings := [];
     other_types := [];
     preprocessor_rws := [];
     type_memory := [];
     all_eq_lemmas := (CONJUNCTS EqualityType_NUM_BOOL))
  fun dest_fun_type ty = let
    val (name,args) = dest_type ty
    in if name = "fun" then (el 1 args, el 2 args) else failwith("not fun type") end
  fun find_type_mapping ty =
    first (fn (t,_) => can (match_type t) ty) (!type_mappings)
  fun free_typevars ty =
    if can dest_vartype ty then [ty] else let
    val (name,tt) = dest_type ty
    in Lib.flatten (map free_typevars tt) end
    handle HOL_ERR _ => []
  fun add_new_type_mapping ty target_ty =
    (type_mappings := (ty,target_ty) :: (!type_mappings))
  fun string_tl s = s |> explode |> tl |> implode
  fun type2t ty =
    if ty = ``:bool`` then ``Tbool`` else
    if ty = ``:int`` then ``Tint`` else
    if ty = ``:num`` then ``Tint`` else
    if can dest_vartype ty then
      mk_comb(``Tvar``,stringSyntax.fromMLstring (string_tl (dest_vartype ty)))
    else let
      val (lhs,rhs) = find_type_mapping ty
      val i = match_type lhs ty
      val xs = free_typevars rhs
      val i = filter (fn {redex = a, residue = _} => mem a xs) i
      val tm = type2t rhs
      val s = map (fn {redex = a, residue = b} => type2t a |-> type2t b) i
      in subst s tm end handle HOL_ERR _ =>
    let
      val (name,tt) = dest_type ty
      val tt = map type2t tt
      val name_tm = stringSyntax.fromMLstring name
      val tt_list = listSyntax.mk_list(tt,type_of ``Tbool``)
      in if name = "fun" then ``Tfn ^(el 1 tt) ^(el 2 tt)`` else
           ``Tapp ^tt_list ^name_tm`` end
  fun inst_type_inv (ty,inv) ty0 = let
    val i = match_type ty ty0
    val ii = map (fn {redex = x, residue = y} => (x,y)) i
    val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
    in subst ss (inst i inv) end
  and list_inst_type_inv ty0 [] = fail()
    | list_inst_type_inv ty0 ((ty,inv)::xs) =
        inst_type_inv (ty,inv) ty0 handle HOL_ERR _ =>
        list_inst_type_inv ty0 xs
  and get_type_inv ty =
    if is_vartype ty then let
      val name = dest_vartype ty |> explode |> tl |> implode
      in mk_var(name,mk_type("fun",[ty,``:v->bool``])) end else
    if can dest_fun_type ty then let
      val (t1,t2) = dest_fun_type ty
      in ``Arrow (^(get_type_inv t1)) (^(get_type_inv t2))`` end else
    if ty = ``:bool`` then ``BOOL`` else
    if ty = ``:num`` then ``NUM`` else
    if ty = ``:int`` then ``INT`` else
      list_inst_type_inv ty (!other_types)
      handle HOL_ERR _ => raise UnsupportedType ty
  fun new_type_inv ty inv = (other_types := (ty,inv) :: (!other_types))
  fun add_type_inv tm target_ty = let
    val ty = fst (dest_fun_type (type_of tm))
    val _ = add_new_type_mapping ty target_ty
    in new_type_inv ty tm end
  fun get_user_supplied_types () = map fst (!other_types)
  fun add_eq_lemma eq_lemma =
    if concl eq_lemma = T then () else
      (all_eq_lemmas := eq_lemma :: (!all_eq_lemmas))
  fun add_type_thms (rws1,rws2,res) = let
    val _ = map (fn (ty,eq_lemma,inv_def,conses,case_lemma,ts) => add_eq_lemma eq_lemma) res
    val _ = (type_memory := map (fn (ty,eq_lemma,inv_def,conses,case_lemma,ts) => (ty,inv_def,conses,case_lemma)) res @ (!type_memory))
    val _ = (preprocessor_rws := rws2 @ (!preprocessor_rws))
    in () end
  fun lookup_type_thms ty = first (fn (ty1,_,_,_) => can (match_type ty1) ty) (!type_memory)
  fun eq_lemmas () = (!all_eq_lemmas)
  fun get_preprocessor_rws () = (!preprocessor_rws)
  (* store/load to/from a single thm *)
  fun pack_types () =
    pack_5tuple
      (pack_list (pack_pair pack_type pack_type))
      (pack_list (pack_pair pack_type pack_term))
      (pack_list pack_thm)
      (pack_list (pack_4tuple pack_type pack_thm (pack_list (pack_pair pack_term pack_thm)) pack_thm))
      (pack_list pack_thm)
        ((!type_mappings), (!other_types), (!preprocessor_rws),
         (!type_memory), (!all_eq_lemmas))
  fun unpack_types th = let
    val (t1,t2,t3,t4,t5) = unpack_5tuple
      (unpack_list (unpack_pair unpack_type unpack_type))
      (unpack_list (unpack_pair unpack_type unpack_term))
      (unpack_list unpack_thm)
      (unpack_list (unpack_4tuple unpack_type unpack_thm (unpack_list (unpack_pair unpack_term unpack_thm)) unpack_thm))
      (unpack_list unpack_thm) th
    val _ = (type_mappings := t1)
    val _ = (other_types := t2)
    val _ = (preprocessor_rws := t3)
    val _ = (type_memory := t4)
    val _ = (all_eq_lemmas := t5)
    in () end
end


(* misc *)

fun get_unique_name str = let
  val names = get_names()
  fun find_name str n = let
    val new_name = str ^ "_" ^ (int_to_string n)
    in if mem new_name names then find_name str (n+1) else new_name end
  fun find_new_name str =
    if mem str names then find_name str 1 else str
  in find_new_name str end

fun dest_args tm =
  let val (x,y) = dest_comb tm in dest_args x @ [y] end
  handle HOL_ERR _ => []

fun D th = let
  val th = th |> DISCH_ALL |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  in if is_imp (concl th) then th else DISCH T th end

val quietDefine = (* quiet version of Define -- by Anthony Fox *)
  Lib.with_flag (Feedback.emit_WARNING, false)
    (Lib.with_flag (Feedback.emit_ERR, false)
       (Lib.with_flag (Feedback.emit_MESG, false)
          (Feedback.trace ("auto Defn.tgoal", 0) TotalDefn.Define)))


(* mapping from dec terms to SML and Ocaml *)

local
  fun dec2str sml d = let (* very slow at the moment *)
    val result =
      ``dec_to_sml_string ^d``
      |> EVAL |> concl |> rand |> stringSyntax.fromHOLstring
      handle HOL_ERR _ => failwith("\nUnable to print "^(term_to_string d)^"\n\n")
    in result end;
in
  fun dec2str_sml d = dec2str true d
end


(* printing output e.g. SML syntax *)

local
  val base_filename = ref "";
  val prelude_decl_count = ref 0;
  datatype print_item = Translation of string * thm | InvDef of thm
  val print_items = ref ([]:print_item list)
  val prelude_name = ref (NONE: string option);
  fun add_print_item i = (print_items := i :: (!print_items))
  val files = ["_ml.txt","_hol.txt","_thm.txt","_ast.txt"]
  fun check_suffix suffix = mem suffix files orelse failwith("bad file suffix")
  fun clear_file suffix = if (!base_filename) = "" then () else let
    val _ = check_suffix suffix
    val t = TextIO.openOut((!base_filename) ^ suffix)
    val _ = TextIO.closeOut(t)
    in () end
  fun get_filename () =
    if !base_filename = "" then let
      val name = current_theory()
      val _ = (base_filename := name)
      val _ = map clear_file files
      in name end
    else !base_filename
  fun append_to_file suffix strs = if get_filename() = "" then () else let
    val _ = check_suffix suffix
    val t = TextIO.openAppend(get_filename() ^ suffix)
    val _ = map (fn s => TextIO.output(t,s)) strs
    val _ = TextIO.closeOut(t)
    in () end
  fun print_decls_aux xs suffix f =
    map (fn tm => append_to_file suffix (f tm)) xs
  fun drop n [] = [] | drop n xs = if n = 0 then xs else drop (n-1) (tl xs)
  fun current_decls () = fst (listSyntax.dest_list (get_decls()))
  fun print_str str = str
  fun print_prelude_comment suffix =
    case !prelude_name of
      NONE => ()
    | SOME name => append_to_file suffix ["\n(* This code extends '"^name^"'. *)\n"]
  fun print_decls () = let
    val ds = drop (!prelude_decl_count) (current_decls ())
    val _ = print "Printing ASTs ... "
    val _ = print_prelude_comment "_ast.txt"
    val _ = print_decls_aux ds "_ast.txt" (fn tm => ["\n",term_to_string tm,"\n"])
    val _ = print "done.\n"
    val _ = print "Printing SML syntax ... "
    val _ = print_prelude_comment "_ml.txt"
    val _ = print_decls_aux ds "_ml.txt" (fn tm => ["\n",print_str (dec2str_sml tm),"\n"])
    val _ = print "done.\n"
    in () end;
  fun print_item (InvDef inv_def) = let
      val th_str = thm_to_string inv_def
      val _ = append_to_file "_thm.txt" ["\nDefinition of refinement invariant:\n\n",th_str,"\n"]
      in () end
    | print_item (Translation (fname,original_def)) = let
      val (th,pre) = get_cert fname
      val def_str = thm_to_string original_def
      val th_str = thm_to_string (D th |> REWRITE_RULE [GSYM CONJ_ASSOC,CONTAINER_def,PRECONDITION_def])
      val _ = append_to_file "_hol.txt" ["\n",def_str,"\n"]
      val _ = append_to_file "_thm.txt" ["\nCertificate theorem for "^fname^":\n\n",th_str,"\n"]
      val _ = if concl pre = T then () else
                append_to_file "_thm.txt" ["\nDefinition of side condition for "^fname^":\n\n",thm_to_string pre,"\n"]
      in () end;
  fun print_decl_abbrev () =
    case get_decl_abbrev () of
      NONE => ()
    | (SOME abbrev_def) => let
      val str = thm_to_string abbrev_def
      val _ = append_to_file "_thm.txt" ["\nDefinition of declaration list:\n\n",str,"\n\n"]
      in () end
  fun print_prelude_name () =
    case !prelude_name of
      NONE => ()
    | SOME name => append_to_file "_thm.txt" ["\nThis translation extends '"^name^"'.\n"]
in
  fun print_reset () =
    (base_filename := "";
     prelude_decl_count := 0;
     print_items := [];
     prelude_name := NONE)
  fun init_printer name = let
    val _ = map clear_file files
    val _ = (prelude_name := SOME name)
    val _ = (prelude_decl_count := (length (current_decls ())))
    in () end
  fun print_translation_output () =
    (print_prelude_name (); map print_item (rev (!print_items));
     print_decl_abbrev (); print_decls ());
  fun print_fname fname def = add_print_item (Translation (fname,def));
  fun print_inv_def inv_def = add_print_item (InvDef inv_def);
end


(* code for loading and storing translations into a single thm *)

local
  val suffix = "_translator_state_thm"
  fun pack_state () = let
    val name = get_module_name () ^ suffix
    val name_tm = stringSyntax.fromMLstring name
    val tag_lemma = ISPEC ``b:bool`` (ISPEC name_tm TAG_def) |> GSYM
    val p1 = pack_certs()
    val p2 = pack_types()
    val p = pack_pair I I (p1,p2)
    val th = PURE_ONCE_REWRITE_RULE [tag_lemma] p
    in save_thm(name,th) end
  fun unpack_state name = let
    val th = fetch name (name ^ suffix)
    val th = PURE_ONCE_REWRITE_RULE [TAG_def] th
    val (p1,p2) = unpack_pair I I th
    val _ = unpack_certs p1
    val _ = unpack_types p2
    in () end;
  val finalised = ref false
in
  fun finalise_reset () = (finalised := false)
  fun finalise_translation () =
    if !finalised then () else let
      val _ = (finalised := true)
      val _ = pack_state ()
      val _ = print_translation_output ()
      in () end
  val _ = Theory.register_hook(
              "miniml.ml_translator",
              (fn TheoryDelta.ExportTheory _ => finalise_translation() | _ => ()))
  fun translation_extends name = let
    val _ = print ("Loading translation: " ^ name ^ " ... ")
    val _ = unpack_state name
    val _ = init_printer name
    val _ = print ("done.\n")
    in () end;
end

(* support for user-defined data-types *)

fun type_of_cases_const ty = let
  val th = TypeBase.case_def_of ty
  val ty = th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
              |> concl |> dest_eq |> fst |> rator |> type_of
  in ty end

fun name_of_type ty = let
  val th = TypeBase.case_def_of ty
  val case_const = th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                      |> concl |> dest_eq |> fst |> repeat rator
  val name = case_const |> dest_const |> fst |> explode |> rev
                        |> funpow 5 tl |> rev |> implode
  in name end;

fun remove_primes th = let
  fun last s = substring(s,size s-1,1)
  fun delete_last_prime s = if last s = "'" then substring(s,0,size(s)-1) else fail()
  fun foo [] ys i = i
    | foo (x::xs) ys i = let
      val name = (fst o dest_var) x
      val new_name = repeat delete_last_prime name
      in if name = new_name then foo xs (x::ys) i else let
        val new_var = mk_var(new_name,type_of x)
        in foo xs (new_var::ys) ((x |-> new_var) :: i) end end
  val i = foo (free_varsl (concl th :: hyp th)) [] []
  in INST i th end

fun get_nchotomy_of ty = let (* ensures that good variables names are used *)
  val case_th = TypeBase.nchotomy_of ty
  val ty0 = type_of (hd (SPEC_ALL case_th |> concl |> free_vars))
  val case_th = INST_TYPE (match_type ty0 ty) case_th
  val xs = map rand (find_terms is_eq (concl case_th))
  val x_var = mk_var("x",ty)
  fun mk_lines [] = []
    | mk_lines (x::xs) = let
    val k = length xs + 1
    fun rename [] = []
      | rename (x::xs) = let val n = int_to_string k ^ "_" ^
                                     int_to_string (length xs + 1)
                          in (x,mk_var("x" ^ n, type_of x),
                                mk_var("v" ^ n,``:v``)) end :: rename xs
    val vars = rev (rename (free_vars x))
    val new_x = subst (map (fn (x,y,z) => x |-> y) vars) x
    val tm = list_mk_exists(rev (free_vars new_x), mk_eq(x_var,new_x))
    in tm :: mk_lines xs end
  val goal = mk_forall(x_var,list_mk_disj (rev (mk_lines xs)))
  val lemma = prove(goal,
    STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `x` case_th)
    \\ FULL_SIMP_TAC (srw_ss()) []);
  in lemma end

fun find_mutrec_types ty = let (* e.g. input ``:v`` gives [``:exp``,``:v``]  *)
  fun is_pair_ty ty = fst (dest_type ty) = "prod"
  fun is_list_ty ty = fst (dest_type ty) = "list"
  fun all_distinct [] = []
    | all_distinct (x::xs) = if mem x xs then all_distinct xs else x :: all_distinct xs
  val xs = snd (TypeBase.size_of ty) |> CONJUNCTS
           |> map (type_of o rand o fst o dest_eq o  concl o SPEC_ALL)
           |> filter (not o is_pair_ty) |> filter (not o is_list_ty)
           |> all_distinct
  in if is_pair_ty ty then [ty] else if length xs = 0 then [ty] else xs end

(*

val pair_SIMP = prove(
  ``!x. pair f1 f2 x v = pair (\y. if y = FST x then f1 y else ARB)
                              (\y. if y = SND x then f2 y else ARB) x v``,
  Cases \\ FULL_SIMP_TAC std_ss [fetch "-" "pair_def"]);

val ty = ``:'a list``
val ty = ``:'a # 'b``
val ty = ``:unit``
val _ = Hol_datatype `TREE = LEAF of 'a | BRANCH of TREE => TREE`;
register_type ty
val _ = Hol_datatype `BTREE = BLEAF of ('a TREE) | BBRANCH of BTREE => BTREE`;
val ty = ``:'a BTREE``
*)

fun clean_lowercase s = let
  fun f c = if #"a" <= c andalso c <= #"z" then implode [c] else
            if #"A" <= c andalso c <= #"Z" then implode [chr (ord c + 32)] else
            if #"0" <= c andalso c <= #"9" then implode [c] else
            if c = #"," then "pair" else
            if mem c [#"_",#"'"] then implode [c] else ""
  in String.translate f s end;

fun clean_uppercase s = let
  fun f c = if #"a" <= c andalso c <= #"z" then implode [chr (ord c - 32)] else
            if #"A" <= c andalso c <= #"Z" then implode [c] else
            if #"0" <= c andalso c <= #"9" then implode [c] else
            if c = #"," then "PAIR" else
            if mem c [#"_",#"'"] then implode [c] else ""
  in String.translate f s end;

fun tag_name type_name const_name = let
  val x = clean_lowercase type_name
  val y = clean_lowercase const_name
  fun upper_case_hd s =
    clean_uppercase (implode [hd (explode s)]) ^ implode (tl (explode s))
  in if y = "" then upper_case_hd x else upper_case_hd y end;

val last_def_fail = ref T

fun derive_record_specific_thms ty = let
  val ty_name = name_of_type ty
  val access_funs =
    TypeBase.accessors_of ty
    |> map (rator o fst o dest_eq o concl o SPEC_ALL)
  val update_funs =
    TypeBase.updates_of ty
    |> map (rator o rator o fst o dest_eq o concl o SPEC_ALL)
  val tm =
    DB.fetch "-" (ty_name ^ "_11")
    |> SPEC_ALL |> concl |> dest_eq |> fst |> dest_eq |> fst
  val xs = dest_args tm
  val c = repeat rator tm
  val case_tm =
    DB.fetch "-" (ty_name ^ "_case_cong")
    |> SPEC_ALL |> UNDISCH_ALL |> concl |> dest_eq |> fst |> repeat rator
  fun prove_accessor_eq (a,x) = let
     val v = mk_var("v",type_of tm)
     val f = foldr (fn (v,tm) => mk_abs(v,tm)) x xs
     val ty1 = case_tm |> type_of |> dest_type  |> snd |> hd
     val i = match_type ty1 (type_of f)
     val rhs = mk_comb(mk_comb(inst i case_tm,f),v)
     val lhs = mk_comb(a,v)
     val goal = mk_forall(v,mk_eq(lhs,rhs))
     val lemma = prove(goal,Cases THEN SRW_TAC [] [])
     in lemma end
  val a_lemmas = map prove_accessor_eq (zip access_funs xs)
  fun prove_updates_eq (a,x) = let
     val v = mk_var("v",type_of tm)
     val t = type_of x
     val g = mk_var("g",mk_type("fun",[t,t]))
     val f = foldr mk_abs (subst [x|->mk_comb(g,x)] tm) xs
     val ty1 = case_tm |> type_of |> dest_type  |> snd |> hd
     val i = match_type ty1 (type_of f)
     val rhs = mk_comb(mk_comb(inst i case_tm,f),v)
     val lhs = mk_comb(mk_comb(a,g),v)
     val goal = mk_forall(v,mk_forall(g,mk_eq(lhs,rhs)))
     val tac = Cases THEN SRW_TAC [] [DB.fetch "-" (ty_name ^ "_fn_updates")]
     in prove(goal,tac) end
  val b_lemmas = map prove_updates_eq (zip update_funs xs)
  val arb = mk_arb(type_of tm)
  val tm2 = foldr (fn ((a,x),y) => mk_comb(``^a (K ^x)``,y)) arb (zip update_funs xs)
  val goal = mk_eq(tm2,tm)
  val rw_lemma = prove(goal,SRW_TAC [] [DB.fetch "-" (ty_name ^ "_component_equality")])
  val rw_lemmas = CONJ (DB.fetch "-" (ty_name ^ "_fupdcanon")) rw_lemma
  in (a_lemmas @ b_lemmas, [rw_lemmas]) end;

fun rename_bound_vars_rule prefix th = let
  val i = ref 0
  fun next_name () = (i:= !i+1; prefix ^ int_to_string (!i))
  fun next_var v = mk_var(next_name (), type_of v)
  fun next_alpha_conv tm = let
    val (v,_) = dest_abs tm
    val _ = not (String.isPrefix prefix (fst (dest_var v))) orelse fail()
    in ALPHA_CONV (next_var v) tm end handle HOL_ERR _ => NO_CONV tm
  in CONV_RULE (DEPTH_CONV next_alpha_conv) th end;

fun get_name ty = clean_uppercase (name_of_type ty) ^ "_TYPE"

fun list_lemma () = let
  val _ = is_const (Parse.Term [ANTIQUOTE ``LIST_TYPE:('a -> v -> bool) -> 'a list -> v -> bool``])
          orelse failwith("LIST_TYPE not yet defined.")
  val list_def = LIST_CONJ [
    EVAL ``LIST_TYPE (a:('a -> v -> bool)) [] v``,
    EVAL ``LIST_TYPE (a:('a -> v -> bool)) (x::xs) v``]
  val LIST_TYPE_SIMP = prove(
    ``!xs b. CONTAINER LIST_TYPE (\x v. if b x \/ MEM x xs then p x v else ARB) xs = LIST_TYPE (p:('a -> v -> bool)) xs``,
    Induct THEN FULL_SIMP_TAC std_ss [FUN_EQ_THM,list_def,MEM,DISJ_ASSOC,CONTAINER_def])
    |> Q.SPECL [`xs`,`\x.F`] |> SIMP_RULE std_ss [] |> GSYM;
  in LIST_TYPE_SIMP end handle HOL_ERR _ => TRUTH;

fun pair_lemma () = let
  val _ = is_const (Parse.Term [ANTIQUOTE ``PAIR_TYPE:('a -> v -> bool) -> ('b -> v -> bool) -> 'a # 'b -> v -> bool``])
          orelse failwith("PAIR_TYPE not yet defined.")
  val pair_def = LIST_CONJ [
    EVAL ``PAIR_TYPE (a:('a -> v -> bool)) (b:('b -> v -> bool)) (x,y) v``]
  val PAIR_TYPE_SIMP = prove(
    ``!x. CONTAINER PAIR_TYPE (\y v. if y = FST x then a y v else ARB)
                              (\y v. if y = SND x then b y v else ARB) x =
          PAIR_TYPE (a:('a -> v -> bool)) (b:('b -> v -> bool)) x``,
    Cases \\ SIMP_TAC std_ss [pair_def,CONTAINER_def,FUN_EQ_THM]) |> GSYM |> SPEC_ALL
  in PAIR_TYPE_SIMP end handle HOL_ERR _ => TRUTH;

(*
  val tys = find_mutrec_types ty
*)

fun define_ref_inv tys = let
  val names = map get_name tys
  val name = hd names
  fun list_mk_type [] ret_ty = ret_ty
    | list_mk_type (x::xs) ret_ty = mk_type("fun",[type_of x,list_mk_type xs ret_ty])
  val cases_thms = map (SPEC_ALL o get_nchotomy_of) tys |> LIST_CONJ
                   |> rename_bound_vars_rule "x_" |> CONJUNCTS
  val all = zip names (zip tys cases_thms) |> map (fn (x,(y,z)) => (x,y,z))
  fun mk_lhs (name,ty,case_th) = let
    val xs = map rand (find_terms is_eq (concl case_th))
    val ty = type_of (hd (SPEC_ALL case_th |> concl |> free_vars))
    val vars = type_vars ty
    val ss = map get_type_inv vars
    val input = mk_var("input",ty)
    val def_name = mk_var(name,list_mk_type (ss @ [input]) ``:v -> bool``)
    val lhs = foldl (fn (x,y) => mk_comb(y,x)) def_name (ss @ [input,``v:v``])
    in (xs,ty,lhs,input) end
  val ys = map mk_lhs all
  fun reg_type (_,ty,lhs,_) = new_type_inv ty (rator (rator lhs));
  val _ = map reg_type ys
  val rw_lemmas = CONJ (list_lemma ()) (pair_lemma ())
  val def_tm = let
    fun mk_lines lhs ty [] input = []
      | mk_lines lhs ty (x::xs) input = let
      val k = length xs + 1
      val tag = tag_name name (repeat rator x |> dest_const |> fst)
      fun rename [] = []
        | rename (x::xs) = let val n = int_to_string k ^ "_" ^
                                       int_to_string (length xs + 1)
                           in (x,mk_var("v" ^ n,``:v``)) end :: rename xs
      val vars = rev (rename (free_vars x))
      val ty_list = mk_type("list",[ty])
      val list_ty = ``:(^ty -> v -> bool) -> ^ty list -> v -> bool``
      fun find_inv tm =
          (mk_comb(get_type_inv (type_of tm),tm))
      val ys = map (fn (y,z) => mk_comb(find_inv y,z)) vars
      val tm = if ys = [] then T else list_mk_conj ys
      val str = stringLib.fromMLstring tag
      val vs = listSyntax.mk_list(map (fn (_,z) => z) vars,``:v``)
      val tm = mk_conj(``v = Conv (^str) ^vs``,tm)
      val tm = list_mk_exists (map (fn (_,z) => z) vars, tm)
      val tm = subst [input |-> x] (mk_eq(lhs,tm))
      (* val vs = filter (fn x => x <> def_name) (free_vars tm) *)
      val ws = free_vars x
      in tm :: mk_lines lhs ty xs input end
    val zs = Lib.flatten (map (fn (xs,ty,lhs,input) => mk_lines lhs ty xs input) ys)
    val def_tm = list_mk_conj zs
    val def_tm = QCONV (REWRITE_CONV [rw_lemmas]) def_tm |> concl |> rand
    in def_tm end
  val size_def = snd (TypeBase.size_of (hd tys))
  fun right_list_dest f tm =
    let val (x,y) = f tm
    in [x] @ right_list_dest f y end handle HOL_ERR _ => [tm]
  fun build_measure [] = fail()
    | build_measure [ty] = let
        val x = fst (TypeBase.size_of ty)
        val xs = tl (tl (right_list_dest dest_fun_type (type_of x)))
        val s = (x |> dest_const |> fst)
        val s1 = foldr (fn (_,s) => s ^ " (K 0)") s xs
        val s2 = foldr (fn (_,s) => s ^ " o SND") " o FST" xs
        in s1 ^ s2  end
    | build_measure (t1::t2::ts) = let
        val s1 = build_measure [t1]
        val s2 = build_measure (t2::ts)
        in "sum_case ("^s1^") ("^s2^")" end
  val tac =
    (WF_REL_TAC [QUOTE ("measure (" ^ build_measure tys ^ ")")]
     \\ REPEAT STRIP_TAC
     \\ TRY (Q.PAT_ASSUM `MEM x xs` (fn th =>
              ASSUME_TAC th THEN Induct_on [ANTIQUOTE (rand (rand (concl th)))]))
     \\ FULL_SIMP_TAC std_ss [MEM,FORALL_PROD,size_def] \\ REPEAT STRIP_TAC
     \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC)
(*
  Define [ANTIQUOTE def_tm]
*)
  val inv_def = tDefine name [ANTIQUOTE def_tm] tac
  val inv_def = CONV_RULE (DEPTH_CONV ETA_CONV) inv_def
  val inv_def = REWRITE_RULE [GSYM rw_lemmas] inv_def
  val _ = save_thm(name ^ "_def",inv_def)
  val ind = fetch "-" (name ^ "_ind") handle HOL_ERR _ => TypeBase.induction_of (hd tys)
(*
  val CHEAT_TAC = ((fn x => ([],fn _ => mk_thm x)) :tactic)
  val inv_def = tDefine name [ANTIQUOTE def_tm] CHEAT_TAC
*)
  fun has_arg_with_type ty line =
    ((line |> SPEC_ALL |> concl |> dest_eq |> fst |> rator |> rand |> type_of) = ty)
  val inv_defs = map (fn ty => (ty,LIST_CONJ (filter (has_arg_with_type ty)
                                     (CONJUNCTS inv_def)))) tys
  (* register the new type invariants *)
  fun sub lhs th = subst [(lhs |> repeat rator) |->
    (th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
        |> concl |> dest_eq |> fst |> repeat rator)] lhs
  val ys2 = map (fn ((_,th),(xs,ty,lhs,input)) => (xs,ty,sub lhs th,input)) (zip inv_defs ys)
  val _ = map reg_type ys2
  (* equality type -- TODO: make this work for mutrec *)
  val eq_lemmas = let
    val tm = inv_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                     |> concl |> dest_eq |> fst |> rator |> rator
    fun list_dest f tm = let val (x,y) = f tm
                         in list_dest f x @ list_dest f y end handle HOL_ERR _ => [tm]
    val xs =
      inv_def |> RW [GSYM CONJ_ASSOC] |> SPEC_ALL |> CONJUNCTS
              |> map (snd o dest_eq o concl o SPEC_ALL)
              |> map (last o list_dest dest_exists)
              |> map (tl o list_dest dest_conj) |> Lib.flatten
              |> map (rator o rator) |> filter (fn t => t <> tm)
    val ys = map (fn tm => ``EqualityType ^tm``) xs
   (* val ys = map (fst o dest_imp o concl o D o SIMP_EqualityType_ASSUMS o ASSUME) ys *)
    val tm1 = ``EqualityType ^tm``
    val ys = filter (fn y => not (mem y [tm1,T])) ys
    val tm2 = if ys = [] then T else list_mk_conj ys
    val goal = mk_imp(tm2,tm1)
    val eq_lemma = prove(goal,
      REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [EqualityType_def]
      \\ STRIP_TAC THEN1
       (REPEAT (Q.PAT_ASSUM `!x1 x2 x3 x4. bbb` (K ALL_TAC))
        \\ (Induct ORELSE Cases)
        \\ SIMP_TAC (srw_ss()) [inv_def,no_closures_def,PULL_EXISTS]
        \\ REPEAT STRIP_TAC \\ RES_TAC)
      THEN1
       (REPEAT (Q.PAT_ASSUM `!x1 x2. bbb ==> bbbb` (K ALL_TAC))
        \\ (Induct ORELSE Cases)
        \\ SIMP_TAC (srw_ss()) [inv_def,no_closures_def,PULL_EXISTS]
        \\ Cases_on `x2` \\ SIMP_TAC (srw_ss()) [inv_def,no_closures_def,PULL_EXISTS]
        \\ REPEAT STRIP_TAC \\ METIS_TAC []))
    (* check that the result does not mention itself *)
    val (tm1,tm2) = dest_imp goal
    val _ = not (can (find_term (fn t => t = rand tm2)) tm1) orelse fail()
    in [eq_lemma] end handle HOL_ERR _ => map (K TRUTH) tys
  val res = map (fn ((th,inv_def),eq_lemma) => (th,inv_def,eq_lemma))
                (zip inv_defs eq_lemmas)
  in res end;

(*
val ty = ``:'a list``; derive_thms_for_type ty
val ty = ``:'a # 'b``; derive_thms_for_type ty
val ty = ``:'a + num``; derive_thms_for_type ty
val ty = ``:num option``; derive_thms_for_type ty
val ty = ``:unit``; derive_thms_for_type ty
*)

fun derive_thms_for_type ty = let
  val (ty,ret_ty) = dest_fun_type (type_of_cases_const ty)
  val is_record = 0 < length(TypeBase.fields_of ty)
  val tys = find_mutrec_types ty
  val name = get_name (hd tys)
  val _ = map (fn ty => print ("Adding type " ^ type_to_string ty ^ "\n")) tys
  (* derive case theorems *)
  val case_thms = map (fn ty => (ty, get_nchotomy_of ty)) tys
  (* define a MiniML datatype declaration *)
  val dtype_parts = map (fn (ty,case_th) => let
    val xs = map rand (find_terms is_eq (concl case_th))
    val y = hd (map (fst o dest_eq) (find_terms is_eq (concl case_th)))
    fun mk_line x = let
      val tag = tag_name name (repeat rator x |> dest_const |> fst)
      val ts = map (type2t o type_of) (dest_args x)
      val tm = pairSyntax.mk_pair(stringSyntax.fromMLstring tag,
                 listSyntax.mk_list(ts,type_of ``Tbool``))
      in tm end
    val lines = listSyntax.mk_list(map mk_line xs,``:tvarN # t list``)
    val (name,ts) = dest_type (type_of y)
    fun string_tl s = s |> explode |> tl |> implode
    val ts = map (stringSyntax.fromMLstring o string_tl o dest_vartype) ts
    val ts_tm = listSyntax.mk_list(ts,``:string``)
    val name_tm = stringSyntax.fromMLstring name
    val dtype = ``(^ts_tm,^name_tm,^lines)``
    in dtype end) case_thms
  val dtype_list = listSyntax.mk_list(dtype_parts,type_of (hd dtype_parts))
  val dtype = ``Dtype ^dtype_list``
  (* define coupling invariant for data refinement and prove EqualityType lemmas *)
  val inv_defs = define_ref_inv tys
  val _ = map (fn (_,inv_def,_) => print_inv_def inv_def) inv_defs
  fun list_mk_type [] ret_ty = ret_ty
    | list_mk_type (x::xs) ret_ty = mk_type("fun",[type_of x,list_mk_type xs ret_ty])

  (* prove lemma for case_of *)
  fun prove_case_of_lemma (ty,case_th,inv_lhs,inv_def) = let
    val cases_th = TypeBase.case_def_of ty
    val (x1,x2) = cases_th |> CONJUNCTS |> hd |> concl |> repeat (snd o dest_forall)
                           |> dest_eq
    val ty1 = x1 |> rand |> type_of
    val ty2 = x2 |> type_of
    val cases_th = INST_TYPE [ty2 |-> ``:'return_type``] cases_th
                   |> INST_TYPE (match_type ty1 ty)
    val cases_tm =
      cases_th |> CONJUNCTS |> hd |> concl |> repeat (snd o dest_forall)
               |> dest_eq |> fst |> rator
    fun rename [] = []
      | rename (x::xs) = let val k = "f" ^ int_to_string (length xs + 1)
                         in (x,mk_var(k,type_of x)) :: rename xs end
    val vs = rev (rename (free_vars cases_tm))
    val cases_tm = subst (map (fn (x,y) => x |-> y) vs) cases_tm
    val exp = ``^cases_tm x``
    val input_var = rand exp
    val ret_ty = type_of exp
    val xs = rev (map rand (find_terms is_eq (concl case_th)))
    fun add_nums [] = []
      | add_nums (x::xs) = (x,length xs+1) :: add_nums xs
    val ys = rev (add_nums (rev (zip (map snd vs) xs)))
    fun str_tl s = implode (tl (explode s))
    fun list_app x [] = x
      | list_app x (y::ys) = list_app (mk_comb(x,y)) ys
    fun mk_vars ((f,tm),n) = let
      val xs = rev (free_vars tm)
      val fxs = list_app f xs
      val pxs = list_app (mk_var("b" ^ int_to_string n,list_mk_type xs ``:bool``)) xs
      val xs = map (fn x => let val s = str_tl (fst (dest_var x)) in
                            (x,mk_var("n" ^ s,``:string``),
                               mk_var("v" ^ s,``:v``)) end) xs
      val exp = mk_var("exp" ^ int_to_string n, ``:exp``)
      in (n,f,fxs,pxs,tm,exp,xs) end
    val ts = map mk_vars ys
    (* patterns *)
    val patterns = map (fn (n,f,fxs,pxs,tm,exp,xs) => let
      val str = tag_name name (repeat rator tm |> dest_const |> fst)
      val str = stringSyntax.fromMLstring str
      val vars = map (fn (x,n,v) => ``Pvar ^n``) xs
      val vars = listSyntax.mk_list(vars,``:pat``)
      in ``(Pcon ^str ^vars, ^exp)`` end) ts
    val patterns = listSyntax.mk_list(patterns,``:pat # exp``)
    val ret_inv = get_type_inv ret_ty
    val result = mk_comb(ret_inv,exp)
    val exp_var = mk_var("exp", ``:exp``)
    val result = ``Eval env (Mat ^exp_var ^patterns) ^result``
    (* assums *)
    val vs = map (fn (n,f,fxs,pxs,tm,exp,xs) => map (fn (x,_,_) => x) xs) ts |> flatten
    val b0 = mk_var("b0",``:bool``)
    fun mk_container tm = mk_comb(``CONTAINER:bool->bool``,tm)
    val tm = b0::map (fn (n,f,fxs,pxs,tm,exp,xs) => mk_imp(mk_container(mk_eq(input_var,tm)),pxs)) ts
             |> list_mk_conj
    val tm = list_mk_forall(vs,tm)
    val result = mk_imp(``TAG () ^tm``,result)
    (* tags *)
    fun find_inv tm =
      if type_of tm = ty then (mk_comb(rator (rator inv_lhs),tm)) else
        (mk_comb(get_type_inv (type_of tm),tm))
    fun mk_hyp (n,f,fxs,pxs,tm,exp,xs) = let
      val env = mk_var("env",``:envE``)
      val env = foldr (fn ((x,n,v),y) =>
        listSyntax.mk_cons(pairSyntax.mk_pair(n,v),y)) env (rev xs)
      val tm = map (fn (x,n,v) => mk_comb(find_inv x,v)) xs @ [pxs]
      val tm = if tm = [] then T else list_mk_conj tm
      val tm = mk_imp(tm,``Eval ^env ^exp (^ret_inv ^fxs)``)
      val vs = map (fn (x,_,_) => x) xs @ map (fn (_,_,v) => v) xs
      val tm = list_mk_forall(vs,tm)
      val n = numSyntax.term_of_int n
      val tm = ``TAG ^n ^tm``
      in tm end;
    (* all_distincts *)
    fun mk_alld (n,f,fxs,pxs,tm,exp,xs) = let
      val tt = listSyntax.mk_list(map (fn (_,x,_) => x) xs,``:string``)
      val tt = mk_comb(``ALL_DISTINCT:string list -> bool``,tt)
      in tt end
    val tt = list_mk_conj(map mk_alld ts) handle HOL_ERR _ => T
    (* goal *)
    val hyps = map mk_hyp ts
    val x = mk_comb(rator (rator inv_lhs),input_var)
    val hyp0 = ``TAG 0 (b0 ==> Eval env ^exp_var ^x)``
    val hyps = list_mk_conj(hyp0::hyps)
    val goal = mk_imp(tt,mk_imp(hyps,result))
    val init_tac =
          PURE_REWRITE_TAC [CONTAINER_def]
          \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `x` case_th)
    fun case_tac n =
          Q.PAT_ASSUM `TAG 0 bbb` (MP_TAC o REWRITE_RULE [TAG_def,inv_def,Eval_def])
          \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
          \\ Q.PAT_ASSUM `TAG () bbb` (STRIP_ASSUME_TAC o remove_primes o
               SPEC_ALL o REWRITE_RULE [TAG_def,inv_def,Eval_def])
          \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT] \\ FULL_SIMP_TAC std_ss [inv_def]
          \\ Q.PAT_ASSUM `TAG ^(numSyntax.term_of_int n) bbb`
               (STRIP_ASSUME_TAC o REWRITE_RULE [TAG_def])
          \\ REPEAT (Q.PAT_ASSUM `TAG xxx yyy` (K ALL_TAC))
          \\ POP_ASSUM (MP_TAC o remove_primes o SPEC_ALL o REWRITE_RULE [Eval_def])
          \\ FULL_SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
          \\ Q.EXISTS_TAC `res'` \\ FULL_SIMP_TAC std_ss []
          \\ ASM_SIMP_TAC (srw_ss()) []
          \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) []
          \\ Q.EXISTS_TAC `res`
          \\ Q.EXISTS_TAC `empty_store` \\ FULL_SIMP_TAC std_ss []
          \\ NTAC (2 * length ts) (ASM_SIMP_TAC (srw_ss())
               [Once evaluate'_cases,pmatch'_def,bind_def,pat_bindings_def])
    val tac = init_tac THENL (map (fn (n,f,fxs,pxs,tm,exp,xs) => case_tac n) ts)
    val case_lemma = prove(goal,tac)
    val case_lemma = case_lemma |> PURE_REWRITE_RULE [TAG_def]
    in (case_lemma,ts) end;
  (* prove lemmas for constructors *)
  fun derive_cons ty inv_lhs inv_def (n,f,fxs,pxs,tm,exp,xs) = let
    val pat = tm
    fun str_tl s = implode (tl (explode s))
    val exps = map (fn (x,_,_) => (x,mk_var("exp" ^ str_tl (fst (dest_var x)), ``:exp``))) xs
    val tag = tag_name name (repeat rator tm |> dest_const |> fst)
    val str = stringLib.fromMLstring tag
    val exps_tm = listSyntax.mk_list(map snd exps,``:exp``)
    val inv = inv_lhs |> rator |> rator
    val result = ``Eval env (Con (^str) ^exps_tm) (^inv ^tm)``
    fun find_inv tm =
      if type_of tm = ty then (mk_comb(rator (rator inv_lhs),tm)) else
        (mk_comb(get_type_inv (type_of tm),tm))
    val tms = map (fn (x,exp) => ``Eval env ^exp ^(find_inv x)``) exps
    val tm = if tms = [] then T else list_mk_conj tms
    val goal = mk_imp(tm,result)
    fun add_primes str 0 = []
      | add_primes str n = mk_var(str,``:v``) :: add_primes (str ^ "'") (n-1)
    val witness = listSyntax.mk_list(add_primes "res" (length xs),``:v``)
    val lemma = prove(goal,
      SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
      \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) [PULL_EXISTS]
      \\ EXISTS_TAC witness \\ ASM_SIMP_TAC (srw_ss()) [inv_def,evaluate_list_SIMP])
    in (pat,lemma) end;

(*
  val ((ty,case_th),(_,inv_def,eq_lemma)) = hd (zip case_thms inv_defs)
*)
  (* call the two functions above for each type *)
  fun make_calls ((ty,case_th),(_,inv_def,eq_lemma)) = let
    val inv_lhs = inv_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                          |> concl |> dest_eq |> fst
    val x = inv_lhs |> rator |> rand
    val input = mk_var("input",type_of x)
    val inv_lhs = subst [x|->input] inv_lhs
    val (case_lemma,ts) = prove_case_of_lemma (ty,case_th,inv_lhs,inv_def)
    val conses = map (derive_cons ty inv_lhs inv_def) ts
    in (ty,eq_lemma,inv_def,conses,case_lemma,ts) end
  val res = map make_calls (zip case_thms inv_defs)
  val _ = snoc_dtype_decl dtype
  val (rws1,rws2) = if not is_record then ([],[]) else derive_record_specific_thms (hd tys)
  in (rws1,rws2,res) end;

local
  val translator = ref (fn th => I (th:thm))
  fun do_translate th = (!translator) th
  fun add_type ty = let
    val (rws1,rws2,res) = derive_thms_for_type ty
    val _ = add_type_thms (rws1,rws2,res)
    val _ = map do_translate rws1
    in res end
  fun lookup_add_type ty = lookup_type_thms ty handle HOL_ERR _ => (add_type ty; lookup_type_thms ty)
  fun conses_of ty = let
    val (ty,inv_def,conses,case_lemma) = lookup_type_thms ty
    in conses end
in
  fun set_translator t = (translator := t)
  fun register_type ty =
    (lookup_add_type ty; ())
    handle UnsupportedType ty1 => (register_type ty1; register_type ty)
  fun cons_for tm = let
    val ty = type_of tm
    val conses = conses_of ty
    val (pat,th) = first (fn (x,th) => can (match_term x) tm) conses
    val i = snd (match_term pat tm)
    val ii = map (fn {redex = x, residue = y} => (x,y)) i
    val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
    in INST ss (INST_TYPE i th) end
    handle HOL_ERR _ => failwith("Not a constructor for a registered type.")
  fun case_of ty = let
    val (ty,inv_def,conses,case_lemma) = lookup_type_thms ty
    in (case_lemma) end
  fun store_eq_thm th = (add_eq_lemma th; th)
end

fun register_term_types tm = let
  fun every_term f tm =
    ((if is_abs tm then every_term f (snd (dest_abs tm)) else
      if is_comb tm then (every_term f (rand tm); every_term f (rator tm)) else ()); f tm)
  val special_types = [``:num``,``:int``,``:bool``] @ get_user_supplied_types ()
  fun ignore_type ty =
    if can (first (fn ty1 => can (match_type ty1) ty)) special_types then true else
    if not (can dest_type ty) then true else
    if can (dest_fun_type) ty then true else false
  fun register_term_type tm = let
    val ty = type_of tm
    in if ignore_type ty then () else (register_type ty) end
  in every_term register_term_type tm end;

(* tests:
register_type ``:'a list``;
register_type ``:'a # 'b``;
register_type ``:'a + num``;
register_type ``:num option``;
register_type ``:unit``;
*)

fun inst_cons_thm tm hol2deep = let
  val th = cons_for tm |> UNDISCH_ALL
  val res = th |> concl |> rand |> rand
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val xs = args res
  val ss = fst (match_term res tm)
  val ys = map (fn x => hol2deep (subst ss x)) xs
  val th1 = if length ys = 0 then TRUTH else LIST_CONJ ys
  in MATCH_MP (D th) th1 end

fun inst_case_thm_for tm = let
  val (_,_,names) = TypeBase.dest_case tm
  val names = map fst names
  val th = case_of (type_of (rand tm))
  val pat = th |> UNDISCH_ALL |> concl |> rand |> rand
  val (ss,i) = match_term pat tm
  val th = INST ss (INST_TYPE i th)
  val ii = map (fn {redex = x, residue = y} => (x,y)) i
  val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
  val th = INST ss th
  val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val ns = map (fn n => (n,args n)) names
  fun rename_var prefix ty v =
    mk_var(prefix ^ implode (tl (explode (fst (dest_var v)))),ty)
  val ts = find_terms (can (match_term ``CONTAINER (b:bool)``)) (concl th)
           |> map (rand o rand)
           |> map (fn tm => (tm,map (fn x => (x,rename_var "n" ``:string`` x,
                                                rename_var "v" ``:v`` x))
                    (dest_args tm handle HOL_ERR _ => [])))
  val ns = map (fn (tm,xs) => let
      val aa = snd (first (fn (pat,_) => can (match_term tm) pat) ns)
      in zip aa xs end) ts |> flatten
  val ms = map (fn (b,(x,n,v)) => n |-> stringSyntax.fromMLstring (fst (dest_var b))) ns
  val th = INST ms th
  val ks = map (fn (b,(x,n,v)) => (fst (dest_var x), fst (dest_var b))) ns @
           map (fn (b,(x,n,v)) => (fst (dest_var v), fst (dest_var b) ^ "{value}")) ns
  fun rename_bound_conv tm = let
    val (v,x) = dest_abs tm
    val (s,ty) = dest_var v
    val new_s = snd (first (fn (z,_) => z = s) ks)
    in ALPHA_CONV (mk_var(new_s,ty)) tm end handle HOL_ERR _ => NO_CONV tm
  val th = CONV_RULE (DEPTH_CONV rename_bound_conv) th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th
  val th = MP th TRUTH
  in th end;

val sat_hyp_lemma = prove(
  ``(b1 ==> (x1 = x2)) /\ (x1 ==> y) ==> b1 /\ x2 ==> y``,
  Cases_on `b1` \\ Cases_on `x1` \\ Cases_on `x2` \\ Cases_on `y` \\ EVAL_TAC);

val last_fail = ref T;
(*
  val tm = !last_fail
*)

fun inst_case_thm tm hol2deep = let
  val th = inst_case_thm_for tm
  val th = CONV_RULE (RATOR_CONV (PURE_REWRITE_CONV [CONJ_ASSOC])) th
  val (hyps,rest) = dest_imp (concl th)
  fun list_dest_forall tm = let
    val (v,tm) = dest_forall tm
    val (vs,tm) = list_dest_forall tm
    in (v::vs,tm) end handle HOL_ERR _ => ([],tm)
  fun take 0 xs = [] | take n xs = hd xs :: take (n-1) (tl xs)
  fun sat_hyp tm = let
    val (vs,x) = list_dest_forall tm
    val (x,y) = dest_imp x
    val z = y |> rand |> rand
    val lemma = hol2deep z
    val lemma = D lemma
    val new_env = y |> rator |> rator |> rand
    val env = mk_var("env",``:envE``)
    val lemma = INST [env|->new_env] lemma
    val (x1,x2) = dest_conj x handle HOL_ERR _ => (T,x)
    val (z1,z2) = dest_imp (concl lemma)
    val thz =
      QCONV (SIMP_CONV std_ss [ASSUME x1,Eval_Var_SIMP,lookup_def] THENC
             DEPTH_CONV stringLib.string_EQ_CONV THENC
             SIMP_CONV std_ss []) z1 |> DISCH x1
    val lemma = MATCH_MP sat_hyp_lemma (CONJ thz lemma)
    val bs = take (length vs div 2) vs
    fun LIST_UNBETA_CONV [] = ALL_CONV
      | LIST_UNBETA_CONV (x::xs) =
          UNBETA_CONV x THENC RATOR_CONV (LIST_UNBETA_CONV xs)
    val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)
                  (LIST_UNBETA_CONV (rev bs))) lemma
    val lemma = GENL vs lemma
    val _ = can (match_term tm) (concl lemma) orelse failwith("sat_hyp failed")
    in lemma end handle HOL_ERR _ => (print_term tm; last_fail := tm; fail())
  fun sat_hyps tm = if is_conj tm then let
    val (x,y) = dest_conj tm
    in CONJ (sat_hyps x) (sat_hyps y) end else sat_hyp tm
  val lemma = sat_hyps hyps
  val th = MATCH_MP th lemma
  val th = CONV_RULE (RATOR_CONV (DEPTH_CONV BETA_CONV THENC
                                  REWRITE_CONV [])) th
  in th end;

fun SIMP_EqualityType_ASSUMS th = let
  val lemmas = eq_lemmas () |> map (UNDISCH_ALL o RW [GSYM AND_IMP_INTRO])
  val th = th |> DISCH_ALL |> PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
  val xs = map (fn th => (concl th,th)) lemmas
  fun find_match [] tm = fail()
    | find_match ((pat,th1)::xs) tm = let
        val (ss,i) = match_term pat tm
        in INST ss (INST_TYPE i th1) end
        handle HOL_ERR _ => find_match xs tm
  fun remove_one th = let
    val hs = hyp th
    val tm = first (can (find_match xs)) hs
    val lemma = find_match xs tm
    val th = MP (DISCH tm th) lemma
    in remove_one th end handle HOL_ERR _ => th
  in remove_one th end;

(* The preprocessor -- returns (def,ind). Here def is the original
   definition stated as a single line:

     foo v1 v2 v3 ... vN = RHS

   where vi are variables. The second return value is an option type:
   if NONE then foo is not recursive, if SOME th then th is an
   induction theorem that matches the structure of foo. *)

fun pattern_complete def vs = let
  val lines = def |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL
                  |> map (fst o dest_eq o concl)
  val const = hd lines |> repeat rator
  val ws = map (fn v => (v,genvar (type_of v))) vs
  val tm = foldl (fn (x,y) => mk_comb(y,snd x)) const ws
  fun tt line = let
    val i = fst (match_term tm line)
    val x = list_mk_exists(rev (free_vars line),
              list_mk_conj (map (fn v => mk_eq(snd v,subst i (snd v))) ws))
    in x end
  val pat_tm = list_mk_disj (map tt lines)
  val pat_tm = subst (map (fn (y,x) => x |-> y) ws) pat_tm
  val pre_tm = ``PRECONDITION ^pat_tm``
  in pre_tm end

fun single_line_def def = let
  val lhs = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                |> concl |> dest_eq |> fst
  val const = lhs |> repeat rator
  fun mk_container tm = ``CONTAINER ^tm``
  in if filter (not o is_var) (dest_args lhs) = [] then (def,NONE) else let
  val name = const |> dest_const |> fst
  val thy = #Thy (dest_thy_const const)
  val rw = fetch thy (name ^ "_curried_def")
           handle HOL_ERR _ =>
           fetch thy (name ^ "_curried_DEF")
           handle HOL_ERR _ => let
           val arg = mk_var("x",const |> type_of |> dest_type |> snd |> hd)
           in REFL (mk_comb(const,arg)) end
  val tpc = rw |> SPEC_ALL |> concl |> dest_eq |> snd |> rator
  val args = rw |> SPEC_ALL |> concl |> dest_eq |> snd |> rand
  val tp = fetch thy (name ^ "_tupled_primitive_def")
           handle HOL_ERR _ =>
           fetch thy (name ^ "_tupled_primitive_DEF")
           handle HOL_ERR _ =>
           fetch thy (name ^ "_primitive_def")
           handle HOL_ERR _ =>
           fetch thy (name ^ "_primitive_DEF")
  val (v,tm) = tp |> concl |> rand |> rand |> dest_abs
  val goal = mk_eq(mk_comb(tpc,args),mk_comb(subst [v|->tpc] tm,args))
  val pre_tm =
    if not (can (find_term is_arb) tm) then T else let
      val vs = rw |> SPEC_ALL |> concl |> dest_eq |> fst |> dest_args
      val pre_tm = pattern_complete def vs
      in pre_tm end
  val goal = mk_imp(pre_tm,goal)
  val lemma = prove(goal,
    SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,GSYM rw]
    \\ REPEAT STRIP_TAC
    \\ CONV_TAC (BINOP_CONV (REWR_CONV (GSYM CONTAINER_def)))
    \\ SRW_TAC [] []
    \\ REPEAT BasicProvers.FULL_CASE_TAC
    \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [def]))
    \\ SRW_TAC [] []
    \\ POP_ASSUM MP_TAC \\ REWRITE_TAC [PRECONDITION_def])
  val lemma = lemma |> RW [] |> UNDISCH_ALL
  val new_def =
    rw |> SPEC_ALL |> CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [lemma]))
       |> CONV_RULE (RAND_CONV BETA_CONV)
       |> REWRITE_RULE [I_THM]
       |> ONCE_REWRITE_RULE [GSYM rw]
  in (new_def,NONE) end handle HOL_ERR _ => let
  val v = mk_var("generated_definition",mk_type("fun",[``:unit``,type_of const]))
  val lemma  = def |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
  val def_tm = (subst [const|->mk_comb(v,``()``)] (concl lemma))
  val _ = quietDefine [ANTIQUOTE def_tm]
  val curried = fetch "-" "generated_definition_curried_def"
  val c = curried |> SPEC_ALL |> concl |> dest_eq |> snd |> rand
  val c2 = curried |> SPEC_ALL |> concl |> dest_eq |> fst
  val c1 = curried |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
  val tupled = fetch "-" "generated_definition_tupled_primitive_def"
  val ind = fetch "-" "generated_definition_ind"
            |> Q.SPEC `\x. very_unlikely_name`
            |> CONV_RULE (DEPTH_CONV BETA_CONV)
            |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss []))
            |> Q.GEN `very_unlikely_name`
  val cc = tupled |> concl |> dest_eq |> fst
  val (v,tm) = tupled |> concl |> rand |> rand |> dest_abs
  val (a,tm) = dest_abs tm
  val tm = (REWRITE_CONV [GSYM FALSE_def,GSYM TRUE_def] THENC
            SIMP_CONV std_ss [Once pair_case_def,GSYM curried]) (subst [a|->c,v|->cc] tm)
           |> concl |> rand |> rator |> rand
  val vs = free_vars tm
  val goal = mk_eq(mk_container c2, mk_container tm)
  val pre_tm =
    if not (can (find_term is_arb) goal) then T else let
      val vs = curried |> SPEC_ALL |> concl |> dest_eq |> fst |> dest_args |> tl
      val pre_tm = pattern_complete def vs
      in pre_tm end
  val vs = filter (fn x => not (mem x vs)) (free_vars goal)
  val goal = subst (map (fn v => v |-> ``():unit``) vs) goal
  val goal = subst [mk_comb(c1,``():unit``)|->const] goal
  val goal = mk_imp(pre_tm,goal)
  val lemma = prove(goal,
    SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,TRUE_def,FALSE_def] \\ SRW_TAC [] []
    \\ REPEAT BasicProvers.FULL_CASE_TAC
    \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [def]))
    \\ SRW_TAC [] [] \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ POP_ASSUM MP_TAC \\ REWRITE_TAC [PRECONDITION_def])
    |> REWRITE_RULE [EVAL ``PRECONDITION T``]
    |> UNDISCH_ALL |> CONV_RULE (BINOP_CONV (REWR_CONV CONTAINER_def))
  in (lemma,SOME ind) end end
  handle HOL_ERR _ => failwith("Preprocessor failed: unable to reduce definition to single line.")

fun remove_pair_abs def = let
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val def = SPEC_ALL def
  fun delete_pair_arg def = let
    val (lhs,rhs) = def |> concl |> dest_eq
    val xs = args lhs
    val p = first pairSyntax.is_pair xs
    val v = hd (rev (free_vars p)) |> dest_var |> fst
    val v = mk_var(v,type_of p)
    val goal = mk_eq(subst [p|->v] lhs,mk_comb(pairSyntax.mk_pabs(p,rhs),v))
    val lemma = prove(goal,
      SPEC_TAC (v,v) \\ FULL_SIMP_TAC std_ss [FORALL_PROD]
      \\ SIMP_TAC std_ss [Once def]);
    in delete_pair_arg lemma end handle HOL_ERR _ => def
  val def = delete_pair_arg def
  val def' = (* if can (find_term (can (match_term ``UNCURRY``))) (concl def) then *)
              CONV_RULE (RAND_CONV (SIMP_CONV std_ss [UNCURRY_SIMP])) def
            (* else def *)
  in if concl def' = T then def else def' end

fun is_rec_def def = let
  val thms = def |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL
  val const = hd thms |> concl |> dest_eq |> fst |> repeat rator
  val rhss = thms |> map (snd o dest_eq o concl)
  in can (first (can (find_term (fn tm => tm = const)))) rhss end

fun is_NONE NONE = true | is_NONE _ = false

fun find_ind_thm def = let
  val const = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL |> concl
                  |> dest_eq |> fst |> repeat rator
  val r = dest_thy_const const
  val ind = fetch (#Thy r) ((#Name r) ^ "_ind")
            handle HOL_ERR _ =>
            fetch (#Thy r) ((#Name r) ^ "_IND")
            handle HOL_ERR _ =>
            fetch (#Thy r) ("ConstMult_ind")
            handle HOL_ERR _ => TRUTH
  in ind end

fun split_let_and_conv tm = let
  val (xs,b) = pairSyntax.dest_anylet tm
  val _ = 1 < length xs orelse fail()
  val _ = map (fn (x,y) => if is_var x then () else fail()) xs
  val ys = map (fn (x,y) => (x,genvar(type_of x),y)) xs
  val b2 = subst (map (fn (x,y,_) => x |-> y) ys) b
  val tm2 = foldr (fn ((x,y,z),b) => pairSyntax.mk_anylet([(y,z)],b)) b2 ys
  val goal = mk_eq(tm,tm2)
  val lemma = prove(goal, REWRITE_TAC [LET_THM] (* potentially bad *)
                          THEN CONV_TAC (DEPTH_CONV BETA_CONV)
                          THEN REWRITE_TAC [])
  in lemma end handle HOL_ERR _ => NO_CONV tm;

local
  val l1 = prove(``~b ==> (b = F)``,REWRITE_TAC [])
  val l2 = prove(``b ==> (b = T)``,REWRITE_TAC [])
in
  fun force_eqns def = let
    fun f th = if is_eq (concl (SPEC_ALL th)) then th else
                 GEN_ALL (MATCH_MP l1 (SPEC_ALL th)) handle HOL_ERR _ =>
                 GEN_ALL (MATCH_MP l2 (SPEC_ALL th))
    in LIST_CONJ (map f (CONJUNCTS (SPEC_ALL def))) end
end

fun preprocess_def def = let
  val def = force_eqns def
  val is_rec = is_rec_def def
  val (def,ind) = single_line_def def
  val def = RW1 [GSYM TRUE_def, GSYM FALSE_def] def
  val def = remove_pair_abs def |> SPEC_ALL
  val def = rename_bound_vars_rule " variable " (GEN_ALL def) |> SPEC_ALL
  val def = CONV_RULE (DEPTH_CONV split_let_and_conv) def
  val ind = if is_rec andalso is_NONE ind then SOME (find_ind_thm def) else ind
  val def = if def |> SPEC_ALL |> concl |> dest_eq |> fst |> is_const
            then SPEC_ALL (RW1 [FUN_EQ_THM] def) else def
  val def = PURE_REWRITE_RULE ([ADD1,boolTheory.literal_case_DEF,
              boolTheory.bool_case_DEF,num_case_thm] @ get_preprocessor_rws()) def
  val def = CONV_RULE (REDEPTH_CONV BETA_CONV) def
  val def = rename_bound_vars_rule "v" (GEN_ALL def) |> SPEC_ALL
  in (is_rec,def,ind) end;


(* definition of the main work horse: hol2deep: term -> thm *)

fun dest_builtin_binop tm = let
  val (px,y) = dest_comb tm
  val (p,x) = dest_comb px
  in (p,x,y,if p = ``($+):num->num->num`` then SPEC_ALL Eval_NUM_ADD else
            if p = ``($-):num->num->num`` then SPEC_ALL Eval_NUM_SUB else
            if p = ``($*):num->num->num`` then SPEC_ALL Eval_NUM_MULT else
            if p = ``($DIV):num->num->num`` then SPEC_ALL Eval_NUM_DIV else
            if p = ``($MOD):num->num->num`` then SPEC_ALL Eval_NUM_MOD else
            if p = ``($<):num->num->bool`` then SPEC_ALL Eval_NUM_LESS else
            if p = ``($<=):num->num->bool`` then SPEC_ALL Eval_NUM_LESS_EQ else
            if p = ``($>):num->num->bool`` then SPEC_ALL Eval_NUM_GREATER else
            if p = ``($>=):num->num->bool`` then SPEC_ALL Eval_NUM_GREATER_EQ else
            if p = ``($+):int->int->int`` then SPEC_ALL Eval_INT_ADD else
            if p = ``($-):int->int->int`` then SPEC_ALL Eval_INT_SUB else
            if p = ``($*):int->int->int`` then SPEC_ALL Eval_INT_MULT else
            if p = ``($/):int->int->int`` then SPEC_ALL Eval_INT_DIV else
            if p = ``($%):int->int->int`` then SPEC_ALL Eval_INT_MOD else
            if p = ``($<):int->int->bool`` then SPEC_ALL Eval_INT_LESS else
            if p = ``($<=):int->int->bool`` then SPEC_ALL Eval_INT_LESS_EQ else
            if p = ``($>):int->int->bool`` then SPEC_ALL Eval_INT_GREATER else
            if p = ``($>=):int->int->bool`` then SPEC_ALL Eval_INT_GREATER_EQ else
            if p = ``($/\):bool->bool->bool`` then SPEC_ALL Eval_And else
            if p = ``($\/):bool->bool->bool`` then SPEC_ALL Eval_Or else
            if p = ``($==>):bool->bool->bool`` then SPEC_ALL Eval_Implies else
              failwith("Not a builtin operator"))
  end

fun inst_Eval_env v th = let
  val thx = th
  val name = fst (dest_var v)
  val str = stringLib.fromMLstring name
  val inv = get_type_inv (type_of v)
  val assum = ``Eval env (Var ^str) (^inv ^v)``
  val new_env = ``(^str,v:v)::env``
  val old_env = new_env |> rand
  val th = thx |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum |> SIMP_RULE bool_ss []
               |> INST [old_env|->new_env]
               |> SIMP_RULE bool_ss [Eval_Var_SIMP,lookup_def]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> SIMP_RULE bool_ss [SafeVar_def]
  val new_assum = fst (dest_imp (concl th))
  val th1 = th |> UNDISCH_ALL
               |> CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV v))
               |> DISCH new_assum
  in th1 end;

fun FORCE_GEN v th1 = GEN v th1 handle HOL_ERR _ => let
  val hs = hyp th1
  val xs = filter (fn tm => mem v (free_vars tm)) hs
  val th2 =  DISCH T th1
  val th3 = foldr (fn (tm,th) => ONCE_REWRITE_RULE [AND_IMP_INTRO] (DISCH tm th)) th2 xs
  val th4 = GEN v th3
  val th4 = HO_MATCH_MP PUSH_FORALL_INTO_IMP th4
  in UNDISCH th4 end

fun apply_Eval_Fun v th fix = let
  val th1 = inst_Eval_env v th
  val th2 = if fix then MATCH_MP Eval_Fun_Eq (GEN ``v:v`` th1)
                   else MATCH_MP Eval_Fun (GEN ``v:v`` (FORCE_GEN v th1))
  in th2 end;

fun apply_Eval_Recclosure fname v th = let
  val vname = fst (dest_var v)
  val vname_str = stringLib.fromMLstring vname
  val fname_str = stringLib.fromMLstring fname
  val body = th |> UNDISCH_ALL |> concl |> rator |> rand
  val inv = get_type_inv (type_of v)
  val new_env = ``(^vname_str,v:v)::(^fname_str,
                    Recclosure env [(^fname_str,^vname_str,^body)] ^fname_str)::env``
  val old_env = ``env:(string # v) list``
  val assum = subst [old_env|->new_env] ``Eval env (Var ^vname_str) (^inv ^v)``
  val thx = th |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum |> SIMP_RULE bool_ss []
               |> INST [old_env|->new_env]
               |> SIMP_RULE bool_ss [Eval_Var_SIMP,lookup_def]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> SIMP_RULE bool_ss [SafeVar_def]
  val new_assum = fst (dest_imp (concl thx))
  val th1 = thx |> UNDISCH_ALL
                |> CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV v))
                |> DISCH new_assum
  val th2 = MATCH_MP Eval_Recclosure (Q.INST [`env`|->`cl_env`] (GEN ``v:v`` th1))
  val assum = ASSUME (fst (dest_imp (concl th2)))
  val th3 = D th2 |> REWRITE_RULE [assum]
  val lemma = MATCH_MP Eval_Eq_Recclosure assum
  val lemma_lhs = lemma |> concl |> dest_eq |> fst
  fun replace_conv tm = let
    val (i,t) = match_term lemma_lhs tm
    in INST i (INST_TYPE t lemma) end handle HOL_ERR _ => NO_CONV tm
  val th4 = CONV_RULE (QCONV (DEPTH_CONV replace_conv)) th3
  in th4 end

fun clean_assumptions th4 = let
  (* lift cl_env assumptions out *)
  val env = mk_var("env",``:(string # v) list``)
  val pattern = ``DeclAssum ds ^env``
  val cl_assums = find_terms (fn tm => can (match_term pattern) tm) (concl th4)
  val th5 = REWRITE_RULE (map ASSUME cl_assums) th4
  (* lift EqualityType assumptions out *)
  val pattern = ``EqualityType (a:'a->v->bool)``
  val eq_assums = find_terms (can (match_term pattern)) (concl th5)
  val th6 = REWRITE_RULE (map ASSUME eq_assums) th5
  in th6 end;

fun get_pre_var lhs fname = let
  fun list_mk_type [] ret_ty = ret_ty
    | list_mk_type (x::xs) ret_ty = mk_type("fun",[type_of x,list_mk_type xs ret_ty])
  val args = dest_args lhs
  val ty = list_mk_type args ``:bool``
  val v = mk_var(fname ^ "_side",ty)
  in (foldl (fn (x,y) => mk_comb(y,x)) v args) end

local
  val rec_pattern = ref T;
  val rec_fname = ref "";
in
  fun install_rec_pattern tm fname =
    (rec_pattern := tm; rec_fname := fname; get_pre_var tm fname)
  fun can_match_rec_pattern tm = can (match_term (!rec_pattern)) tm
  fun uninstall_rec_pattern () = (rec_pattern := ``ARB:bool``)
  fun rec_fun () = repeat rator (!rec_pattern)
  fun rec_term () = (!rec_pattern)
  fun rec_name () = (!rec_fname)
  fun rec_pre_var () = get_pre_var (!rec_pattern) (!rec_fname)
end

fun check_inv name tm result = let
  val tm2 = result |> concl |> rand |> rand
  in if aconv tm2 tm then result else let
    val _ = print ("\n\nhol2deep failed at '" ^ name ^ "'\n\ntarget:\n\n")
    val _ = print_term tm
    val _ = print "\n\nbut derived:\n\n"
    val _ = print_term tm2
    val _ = print "\n\n\n"
    in failwith("checkinv") end end

fun MY_MATCH_MP th1 th2 = let
  val tm1 = fst (dest_imp (concl th1))
  val tm2 = concl th2
  val (s,i) = match_term tm1 tm2
  in MP (INST s (INST_TYPE i th1)) th2 end;

fun force_remove_fix thx = let
  val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
  val xs = map rand (find_terms (can (match_term pat)) (concl thx))
  val s = SIMP_RULE std_ss [Eval_FUN_FORALL_EQ,FUN_QUANT_SIMP]
  val thx = foldr (fn (x,th) => s (FORCE_GEN x th)) thx xs
  in thx end;

fun rm_fix res = let
  val lemma = mk_thm([],``Eq b x = b``)
  val tm2 = QCONV (REWRITE_CONV [lemma]) res |> concl |> dest_eq |> snd
  in tm2 end

val MAP_pattern = ``MAP (f:'a->'b)``

(*
val tm = rhs

val tm = ``MAP (\v3. type_subst v6 v3) args``
val tm = ``MAP (\v3. type_subst v6 v3)``

*)

fun hol2deep tm =
  (* variables *)
  if is_var tm then let
    val (name,ty) = dest_var tm
    val inv = get_type_inv ty
    val str = stringSyntax.fromMLstring name
    val result = ASSUME (mk_comb(``Eval env (Var ^str)``,mk_comb(inv,tm)))
    in check_inv "var" tm result end else
  (* constants *)
  if numSyntax.is_numeral tm then SPEC tm Eval_Val_NUM else
  if intSyntax.is_int_literal tm then SPEC tm Eval_Val_INT else
  if (tm = T) orelse (tm = F) then SPEC tm Eval_Val_BOOL else
  if (tm = ``TRUE``) orelse (tm = ``FALSE``) then SPEC tm Eval_Val_BOOL else
  (* data-type constructor *)
  inst_cons_thm tm hol2deep handle HOL_ERR _ =>
  (* data-type pattern-matching *)
  inst_case_thm tm hol2deep handle HOL_ERR _ =>
  (* recursive pattern *)
  if can_match_rec_pattern tm then let
    fun dest_args tm = rand tm :: dest_args (rator tm) handle HOL_ERR _ => []
    val xs = dest_args tm
    val f = rec_fun ()
    val str = stringLib.fromMLstring (rec_name())
    fun mk_fix tm = let
      val inv = get_type_inv (type_of tm)
      in ``Eq ^inv ^tm`` end
    fun mk_arrow x y = ``Arrow ^x ^y``
    fun mk_inv [] res = res
      | mk_inv (x::xs) res = mk_inv xs (mk_arrow (mk_fix x) res)
    val inv = mk_inv xs (get_type_inv (type_of tm))
    val ss = fst (match_term (rec_term ()) tm)
    val pre = subst ss (rec_pre_var ())
    val h = ASSUME ``PreImp ^pre (Eval env (Var ^str) (^inv ^f))``
            |> RW [PreImp_def] |> UNDISCH
    val ys = map (fn tm => MATCH_MP Eval_Eq (hol2deep tm)) xs
    fun apply_arrow hyp [] = hyp
      | apply_arrow hyp (x::xs) =
          MATCH_MP (MATCH_MP Eval_Arrow (apply_arrow hyp xs)) x
    val result = apply_arrow h ys
    in check_inv "rec_pattern" tm result end else
  (* previously translated term *)
  if can lookup_cert tm then let
    val th = lookup_cert tm
    val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
    val xs = find_terms (can (match_term pat)) (concl th) |> map rand
    val ss = map (fn v => v |-> genvar(type_of v)) xs
    val th = INST ss th
    val res = th |> UNDISCH_ALL |> concl |> rand
    val inv = get_type_inv (type_of tm)
    val target = mk_comb(inv,tm)
    val (ss,ii) = match_term res target handle HOL_ERR _ =>
                  match_term (rm_fix res) (rm_fix target) handle HOL_ERR _ => ([],[])
    val result = INST ss (INST_TYPE ii th)
    in check_inv "lookup_cert" tm result end else
  (* built-in binary operations *)
  if can dest_builtin_binop tm then let
    val (p,x1,x2,lemma) = dest_builtin_binop tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    val result = MATCH_MP (MATCH_MP lemma th1) (UNDISCH_ALL th2) |> UNDISCH_ALL
    in check_inv "binop" tm result end else
  (* boolean not *)
  if can (match_term ``~(b:bool)``) tm then let
    val x1 = rand tm
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_Bool_Not th1
    in check_inv "not" tm result end else
  (* equality: n = 0 *)
  if can (match_term ``(n = (0:num))``) tm then let
    val x1 = fst (dest_eq tm)
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_NUM_EQ_0 th1
    in check_inv "num_eq_0" tm result end else
  (* equality: 0 = n *)
  if can (match_term ``(0 = (n:num))``) tm then let
    val x1 = snd (dest_eq tm)
    val th1 = hol2deep x1
    val result = MATCH_MP (GSYM Eval_NUM_EQ_0) th1
    in check_inv "0_eq_num" tm result end else
  (* equality *)
  if is_eq tm then let
    val (x1,x2) = dest_eq tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    val result = MATCH_MP Eval_Equality (CONJ th1 th2) |> UNDISCH
    in check_inv "equal" tm result end else
  (* if statements *)
  if is_cond tm then let
    val (x1,x2,x3) = dest_cond tm
    val th1 = hol2deep x1
    val th2 = hol2deep x2
    val th3 = hol2deep x3
    val th = MATCH_MP Eval_If (LIST_CONJ [D th1, D th2, D th3])
    val result = UNDISCH th
    in check_inv "if" tm result end else
  (* let expressions *)
  if can dest_let tm andalso is_abs (fst (dest_let tm)) then let
    val (x,y) = dest_let tm
    val (v,x) = dest_abs x
    val th1 = hol2deep y
    val th2 = hol2deep x
    val th2 = inst_Eval_env v th2
    val th2 = th2 |> GEN ``v:v``
    val z = th1 |> concl |> rand |> rand
    val th2 = INST [v|->z] th2
    val result = MATCH_MP Eval_Let (CONJ th1 th2)
    in check_inv "let" tm result end else
  (* special pattern *) let
    val _ = match_term MAP_pattern tm
    val (m,f) = dest_comb tm
    val th_m = hol2deep ``MAP:('a->'b) -> 'a list -> 'b list``
    val (v,x) = dest_abs f
    val th_f = hol2deep x
    val th_f = apply_Eval_Fun v th_f true
    val thi = th_f |> DISCH_ALL |> RW [AND_IMP_INTRO] |> GEN v
    val thi = HO_MATCH_MP Eq_IMP_And thi
    val thi = MATCH_MP (MATCH_MP Eval_Arrow th_m) thi
    val list_type_def = fetch "-" "LIST_TYPE_def"
    val LIST_TYPE_And = prove(
     ``LIST_TYPE (And a P) = And (LIST_TYPE a) (EVERY (P:'a->bool))``,
     SIMP_TAC std_ss [FUN_EQ_THM,And_def] \\ Induct
     \\ FULL_SIMP_TAC std_ss [MEM,list_type_def]
     \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
     \\ FULL_SIMP_TAC (srw_ss()) [And_def])
    val thi = RW [LIST_TYPE_And] thi
    val thi = MATCH_MP And_IMP_Eq thi |> SIMP_RULE std_ss [EVERY_MEM]
    val thi = thi |> CONV_RULE ((RATOR_CONV o RAND_CONV) (REWR_CONV (GSYM PRECONDITION_def)))
    val result = thi |> UNDISCH_ALL
    in check_inv "map" tm result end handle HOL_ERR _ =>
  (* normal function applications *)
  if is_comb tm then let
    val (f,x) = dest_comb tm
    val thf = hol2deep f
    val thx = hol2deep x
    val thx = force_remove_fix thx
    val result = MATCH_MP (MATCH_MP Eval_Arrow thf) thx handle HOL_ERR _ =>
                 MY_MATCH_MP (MATCH_MP Eval_Arrow thf) (MATCH_MP Eval_Eq thx)
    in check_inv "comb" tm result end else
  (* lambda applications *)
  if is_abs tm then let
    val (v,x) = dest_abs tm
    val thx = hol2deep x
    val result = apply_Eval_Fun v thx false
    in check_inv "abs" tm result end else
  if is_arb tm then let
    val inv = get_type_inv (type_of tm)
    val goal = ``PRECONDITION F ==> Eval env (Raise Bind_error) (^inv ^tm)``
    val result = prove(goal,SIMP_TAC std_ss [PRECONDITION_def]) |> UNDISCH
    in check_inv "arb" tm result end
  else raise (UnableToTranslate tm)

fun hol2val tm = let
  val th_rhs = hol2deep tm
  val res = mk_comb(rand (concl th_rhs),mk_var("v",``:v``))
            |> EVAL |> SIMP_RULE std_ss [] |> concl |> rand |> rand
  in res end;

(*
val tm = f
val tm = rhs
val tm = z
*)

(* collect precondition *)

val PRECONDITION_EQ_CONTAINER = prove(
  ``(PRECONDITION p = CONTAINER p) /\
    (CONTAINER ~p = ~CONTAINER p) /\ CONTAINER T``,
  EVAL_TAC);

val CONTAINER_NOT_ZERO = prove(
  ``!P. (~(CONTAINER (b = 0)) ==> P b) =
        !n. (CONTAINER (b = SUC n)) ==> P (SUC n:num)``,
  REPEAT STRIP_TAC THEN Cases_on `b`
  THEN EVAL_TAC THEN SRW_TAC [] [ADD1]);

fun clean_precondition pre_def = let
  val th = SIMP_RULE (srw_ss()) [] pre_def
  val th = REWRITE_RULE [CONTAINER_def] th
  val th = rename_bound_vars_rule "v" (GEN_ALL th) |> SPEC_ALL
  in th end;

fun extract_precondition th pre_var is_rec =
  if not is_rec then if is_imp (concl th) then let
    val c = (REWRITE_CONV [CONTAINER_def,PRECONDITION_def] THENC
             ONCE_REWRITE_CONV [GSYM PRECONDITION_def])
    val c = (RATOR_CONV o RAND_CONV) c
    val th = CONV_RULE c th
    val rhs = th |> concl |> dest_imp |> fst |> rand
    in if free_vars rhs = [] then
      (UNDISCH_ALL (SIMP_RULE std_ss [EVAL ``PRECONDITION T``] th),NONE)
    else let
    val def_tm = mk_eq(pre_var,rhs)
    val pre_def = quietDefine [ANTIQUOTE def_tm]
    val c = REWR_CONV (GSYM pre_def)
    val c = (RATOR_CONV o RAND_CONV o RAND_CONV) c
    val th = CONV_RULE c th |> UNDISCH_ALL
    val pre_def = clean_precondition pre_def
    in (th,SOME pre_def) end end else (th,NONE)
  else let
  fun rename_bound_vars_rule th = let
    val i = ref 0
    fun next_name () = (i:= !i+1; "v__" ^ int_to_string (!i))
    fun next_var v = mk_var(next_name (), type_of v)
    fun next_alpha_conv tm = let
      val (v,_) = dest_abs tm
      val _ = not (String.isPrefix "v__" (fst (dest_var v))) orelse fail()
      in ALPHA_CONV (next_var v) tm end handle HOL_ERR _ => NO_CONV tm
    in CONV_RULE (DEPTH_CONV next_alpha_conv) th end
  val th = SIMP_RULE bool_ss [CONTAINER_NOT_ZERO] th
  val th = rename_bound_vars_rule th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (REWRITE_CONV [GSYM AND_IMP_INTRO])) th
  val tm = concl th |> dest_imp |> fst
  fun replace_any_match pat tm = let
    val xs = find_terms (can (match_term pat)) tm
    in subst (map (fn x => x |-> T) xs) tm end
  val rw1 = mk_thm([],``PRECONDITION b = T``)
  val tm1 = QCONV (REWRITE_CONV [rw1]) tm |> concl |> rand
  val pat = Eval_def |> SPEC_ALL |> concl |> dest_eq |> fst
  val rw2 = mk_thm([],pat)
  val tm2 = QCONV (REWRITE_CONV [rw2,PreImp_def]) tm |> concl |> rand
  (* check whether the precondition is T *)
  val (no_pre,th5) = let
    val pre_v = repeat rator pre_var
    val true_pre = list_mk_abs ((dest_args pre_var), T)
    val tm3 = subst [pre_v |-> true_pre] tm2
    val res = QCONV (REWRITE_CONV [rw2,PreImp_def,PRECONDITION_def,CONTAINER_def]) tm3 |> concl |> rand
    val th5 = INST [pre_v |-> true_pre] th
                |> SIMP_RULE bool_ss [PRECONDITION_EQ_CONTAINER]
                |> PURE_REWRITE_RULE [PreImp_def,PRECONDITION_def]
                |> CONV_RULE (DEPTH_CONV BETA_CONV THENC
                              (RATOR_CONV o RAND_CONV) (REWRITE_CONV []))
    in (res = T, th5) end
  in if no_pre then (th5,NONE) else let
  (* define precondition *)
  fun list_dest_forall tm = let
    val (v,tm) = dest_forall tm
    val (vs,tm) = list_dest_forall tm
    in (v::vs,tm) end handle HOL_ERR _ => ([],tm)
  fun my_list_mk_conj [] = T
    | my_list_mk_conj xs = list_mk_conj xs
  fun list_dest f tm = let val (x,y) = f tm
                       in list_dest f x @ list_dest f y end handle HOL_ERR _ => [tm]
  val list_dest_conj = list_dest dest_conj
  val tms = list_dest_conj tm2
  val tm = first is_forall tms handle HOL_ERR _ => first is_imp tms
  val others = my_list_mk_conj (filter (fn x => x <> tm) tms)
  val pat = ``CONTAINER (x = y:'a) ==> z``
  fun dest_container_eq_imp tm = let
    val _ = match_term pat tm
    val (xy,z) = dest_imp tm
    val (x,y) = dest_eq (rand xy)
    val _ = dest_var x
    in (x,y,z) end
  fun cons_fst x (y,z) = (x::y,z)
  fun dest_forall_match tm = let
    val xs = list_dest_conj (snd (list_dest_forall tm))
             |> map dest_container_eq_imp
    val ys = map (fn (x,y,z) => map (cons_fst (x,y)) (dest_forall_match z)) xs
    in Lib.flatten ys end handle HOL_ERR _ => [([],tm)]
  val vs = dest_args pre_var
  val ws = map (fn v => (v,mk_var(fst (dest_var v) ^ "AA",type_of v))) vs
  val xs = map (fn (x,y) => (x,y,others)) (dest_forall_match tm @ [(ws,T)])
  fun process_line (x,y,z) = let
    val (x1,x2) = foldl (fn ((x1,x2),(z1,z2)) => (subst [x1 |-> x2] z1, subst [x1 |-> x2] z2)) (pre_var,z) x
    fun simp tm = QCONV (SIMP_CONV (srw_ss()) [PRECONDITION_def]) tm |> concl |> rand
    in mk_eq(x1,simp(mk_conj(y,x2))) end
  val def_tm = list_mk_conj (map process_line xs)
  fun alternative_definition_of_pre pre_var tm2 = let
    val rw = QCONV (REWRITE_CONV [PRECONDITION_def,CONTAINER_def]) tm2
    val gg = rw |> concl |> dest_eq |> snd
    val gg = (mk_imp(gg,pre_var))
    val (_,_,pre_def) = Hol_reln [ANTIQUOTE gg]
    val const = pre_def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
    val v = repeat rator pre_var
    in subst [v|->const] tm2 |> (REWR_CONV rw THENC REWR_CONV (GSYM pre_def))
       |> GSYM end
  val pre_def = quietDefine [ANTIQUOTE def_tm]
                handle HOL_ERR _ =>
                alternative_definition_of_pre pre_var tm2
  val pre_def = fst (single_line_def pre_def)
  val pre_const = pre_def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
  val pre_v = pre_var |> repeat rator
  (* prove pre is sufficient *)
  val s = subst [pre_v|->pre_const]
  val goal = mk_imp(s pre_var, s tm2)
  val pre_thm = prove(goal,
    CONV_TAC (RATOR_CONV (PURE_ONCE_REWRITE_CONV [pre_def]))
    THEN REPEAT BasicProvers.FULL_CASE_TAC
    THEN FULL_SIMP_TAC (srw_ss()) [PULL_FORALL,CONTAINER_def,
      PRECONDITION_def,PreImp_def])
  (* simplify main thm *)
  val goal_lhs = mk_conj(subst [pre_v|->pre_const] tm1,
                     subst [pre_v|->pre_const] pre_var)
  val th = INST [pre_v|->pre_const] th
  val tm = concl th |> dest_imp |> fst
  val goal = mk_imp(goal_lhs,tm)
  val lemma = prove(goal,STRIP_TAC THEN IMP_RES_TAC pre_thm THEN METIS_TAC [])
  val th = MP th (UNDISCH lemma)
  val th = th |> DISCH goal_lhs
  val th = MATCH_MP IMP_PreImp th
  val pre_def = clean_precondition pre_def
  in (th,SOME pre_def) end end


(* main translation routines *)

(*
val def = HD; translate def;
*)

fun translate def = let
  val original_def = def
  fun the (SOME x) = x | the _ = failwith("the of NONE")
  (* perform preprocessing -- reformulate def *)
  val (is_rec,def,ind) = preprocess_def def
  val (lhs,rhs) = dest_eq (concl def)
  val fname = repeat rator lhs |> dest_const |> fst |> get_unique_name
  val _ = print ("Translating " ^ fname ^ "\n")
  val fname_str = stringLib.fromMLstring fname
  (* read off information *)
  val _ = register_term_types (concl def)
  fun rev_param_list tm = rand tm :: rev_param_list (rator tm) handle HOL_ERR _ => []
  val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
  val no_params = (length rev_params = 0)
  (* derive deep embedding *)
  val pre_var = install_rec_pattern lhs fname
  val th = hol2deep rhs
  val _ = uninstall_rec_pattern ()
  (* replace rhs with lhs in th *)
  val th = CONV_RULE ((RAND_CONV o RAND_CONV)
             (REWRITE_CONV [CONTAINER_def] THENC ONCE_REWRITE_CONV [GSYM def])) th
  (* optimise generated code *)
  val th = MATCH_MP Eval_OPTIMISE (UNDISCH_ALL th)
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th
  val th = D th
  (* abstract parameters *)
  val (th,v) = if no_params then (th,T) else
                 (foldr (fn (v,th) => apply_Eval_Fun v th true) th
                    (rev (if is_rec then butlast rev_params else rev_params)),
                  last rev_params)
  val th = if not is_rec then D (clean_assumptions th)
           else apply_Eval_Recclosure fname v th |> clean_assumptions
  val th = CONV_RULE (QCONV (DEPTH_CONV ETA_CONV)) th
  val th = if is_rec then Q.INST [`shaddow_env`|->`cl_env`] th |> REWRITE_RULE []
                     else Q.INST [`shaddow_env`|->`env`] th |> REWRITE_RULE []
  (* collect precondition *)
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
                      (SIMP_CONV std_ss [EVAL ``CONTAINER TRUE``,
                                         EVAL ``CONTAINER FALSE``])) th
  val th = clean_assumptions th
  val (th,pre) = if no_params then (th,NONE) else extract_precondition th pre_var is_rec
  (* apply induction *)
  val th = if not is_rec then th else let
    val th = REWRITE_RULE [CONTAINER_def] th
    val hs = hyp th
    val hyp_tm = list_mk_abs(rev rev_params, th |> UNDISCH_ALL |> concl)
    val goal = list_mk_forall(rev rev_params, th |> UNDISCH_ALL |> concl)
    val goal = mk_imp(list_mk_conj hs,goal)
    val ind_thm = (the ind)
    val ind_thm = rename_bound_vars_rule "i" ind_thm
                  |> SIMP_RULE std_ss []
(*
    set_goal([],goal)
*)
    val lemma = prove(goal,
      STRIP_TAC
      \\ SIMP_TAC std_ss [FORALL_PROD]
      \\ MATCH_MP_TAC (SPEC hyp_tm ind_thm |> CONV_RULE (DEPTH_CONV BETA_CONV))
      \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC th
      \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
      \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
      \\ FULL_SIMP_TAC std_ss [pair_case_def]
      \\ METIS_TAC []);
    val th = UNDISCH lemma |> SPECL (rev rev_params)
    val th = RW [PreImp_def] th |> UNDISCH_ALL
    in th end
  (* remove Eq *)
  fun f (v,th) =
    HO_MATCH_MP Eval_FUN_FORALL (GEN v th) |> SIMP_RULE std_ss [FUN_QUANT_SIMP]
  val th = foldr f th rev_params handle HOL_ERR _ => th
  (* simpliy EqualityType *)
  val th = SIMP_EqualityType_ASSUMS th
  (* abbreviate code *)
  val th = th |> DISCH_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
  val th = if is_rec then
             th |> DISCH (first (can (find_term (fn tm => tm = ``Recclosure``))) (hyp th))
                |> Q.INST [`cl_env`|->`env`,`env`|->`env1`] |> DISCH (get_DeclAssum ())
                |> Q.GEN `env` |> Q.GEN `env1`
                |> REWRITE_RULE [Eval_Var_EQ,AND_IMP_INTRO]
                |> MATCH_MP DeclAssum_Dletrec_INTRO |> Q.SPEC `env` |> UNDISCH_ALL
           else
             th |> DISCH (get_DeclAssum ()) |> Q.GEN `env`
                |> MATCH_MP DeclAssum_Dlet_INTRO
                |> SPEC fname_str |> Q.SPEC `env` |> UNDISCH_ALL
  (* store certificate for later use *)
  val pre = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
  val th = store_cert th pre |> Q.SPEC `env` |> UNDISCH_ALL
  val _ = print_fname fname original_def
  in th end handle UnableToTranslate tm => let
    val _ = print "\n\nCannot translate term:  "
    val _ = print_term tm
    val _ = print "\n\nwhich has type:\n\n"
    val _ = print_type (type_of tm)
    val _ = print "\n\n"
    in raise UnableToTranslate tm end;

val _ = set_translator translate;

fun mlDefine q = let
  val def = Define q
  val th = translate def
  val _ = print "\n"
  val _ = print_thm (D th)
  val _ = print "\n\n"
  in def end;

fun mltDefine name q tac = let
  val def = tDefine name q tac
  val th = translate def
  val _ = print "\n"
  val _ = print_thm (D th)
  val _ = print "\n\n"
  in def end;

fun reset_translation () =
  (cert_reset(); type_reset(); print_reset(); finalise_reset());

end
