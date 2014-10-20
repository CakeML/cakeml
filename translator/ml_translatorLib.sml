structure ml_translatorLib (* :> ml_translatorLib *) =
struct

open HolKernel boolLib bossLib;

open astTheory libTheory semanticPrimitivesTheory bigStepTheory print_astTheory;
open terminationTheory print_astTerminationTheory stringLib;
open ml_translatorTheory intLib lcsymtacs;
open arithmeticTheory listTheory combinTheory pairTheory pairLib;
open integerTheory intLib ml_optimiseTheory;

infix \\ val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

fun print_time s f x = f x
(*
let
  val () = print "Starting "
  val () = print s
  val () = print "...\n"
  val r = time f x
  val () = print s
  val () = print " done\n"
in r end
*)

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

fun pack_option f1 NONE = pack_list I []
  | pack_option f1 (SOME x) = pack_list I [f1 x]
fun unpack_option f1 th =
  let val x = unpack_list I th in
    case x of [] => NONE | (x::xs) => SOME (f1 x) end

fun pack_triple f1 f2 f3 (x1,x2,x3) = pack_list I [f1 x1, f2 x2, f3 x3]
fun unpack_triple f1 f2 f3 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x), f3 (el 3 x)) end

fun pack_4tuple f1 f2 f3 f4 (x1,x2,x3,x4) = pack_list I [f1 x1, f2 x2, f3 x3, f4 x4]
fun unpack_4tuple f1 f2 f3 f4 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x), f3 (el 3 x), f4 (el 4 x)) end

fun pack_5tuple f1 f2 f3 f4 f5 (x1,x2,x3,x4,x5) = pack_list I [f1 x1, f2 x2, f3 x3, f4 x4, f5 x5]
fun unpack_5tuple f1 f2 f3 f4 f5 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x), f3 (el 3 x), f4 (el 4 x), f5 (el 5 x)) end

fun pack_6tuple f1 f2 f3 f4 f5 f6 (x1,x2,x3,x4,x5,x6) = pack_list I [f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6]
fun unpack_6tuple f1 f2 f3 f4 f5 f6 th =
  let val x = unpack_list I th in (f1 (el 1 x), f2 (el 2 x), f3 (el 3 x), f4 (el 4 x), f5 (el 5 x), f6 (el 6 x)) end


exception UnableToTranslate of term;
exception UnsupportedType of hol_type;

(* code for managing state of certificate theorems *)

fun take 0 xs = []
  | take n [] = []
  | take n (x::xs) = x :: take (n-1) xs

fun MY_MP name th1 th2 =
  MP th1 th2 handle e =>
    let
      val _ = print ("\n\n "^name^" MP th1 th2 failed, th1 is:\n\n")
      val _ = print_thm th1
      val _ = print "\n\nth2 is:\n\n"
      val _ = print_thm th2
      val _ = print "\n\n"
    in raise e end

fun prove (goal,tac) = let
  val (rest,validation) = tac ([],goal)
  in if length rest = 0 then validation [] else let
  in failwith "prove failed" end end

fun auto_prove proof_name (goal,tac) = let
  val (rest,validation) = tac ([],goal) handle Empty => fail()
  in if length rest = 0 then validation [] else let
  in failwith("auto_prove failed for " ^ proof_name) end end

local
  (* inv: get_DeclAssum () is a hyp in each thm in each !cert_memory *)
  val decl_abbrev = ref TRUTH;
  val decl_term   = ref ``[]:dec list``;
  val cert_memory = ref ([] : (string * term * thm * thm) list);
  val cenv_eq_thm = ref (DeclAssumCons_NIL |> GEN_ALL |> Q.SPEC `NONE`)
  val decl_exists = ref (DeclAssumExists_NIL |> GEN_ALL |> Q.SPEC `NONE`)
  (* session specific state below *)
  val decl_name = ref "";
  val abbrev_counter = ref 0;
  val abbrev_defs = ref ([]:thm list);
in
  fun get_mn () = (!decl_exists) |> concl |> rator |> rand
  fun INST_mn th = INST [``mn:string option`` |-> get_mn()] th
  fun full_id name =
    if aconv (get_mn ()) ``NONE:string option`` then ``Short ^name``
    else ``Long ^(get_mn () |> rand) ^name``
  fun translate_into_module name =
    if not (aconv (!decl_term) ``[]:dec list``) then
      failwith "translate_into_module can only be used on an empty translation"
    else let
      val _ = print ("\n\nTranslating into module: " ^ name ^ "\n\n")
      val tm = optionSyntax.mk_some(stringSyntax.fromMLstring name)
      val _ = (cenv_eq_thm := (DeclAssumCons_NIL |> GEN_ALL |> SPEC tm))
      val _ = (decl_exists := (DeclAssumExists_NIL |> GEN_ALL |> SPEC tm))
      in () end;
  fun get_cenv_eq_thm () = !cenv_eq_thm
  fun get_cenv_names () = let
    val th = get_cenv_eq_thm ()
    val pat = full_id ``(n:string)``
    val strs1 = find_terms (can (match_term pat)) (concl th) |> map rand
    val pat = ``(n:string,x:'a)``
    val strs2 = find_terms (can (match_term pat)) (concl th) |> map (rand o rator)
    val strs = strs1 @ strs2
    fun all_distinct [] = []
      | all_distinct (x::xs) = let
        val ys = all_distinct xs
        in if mem x ys then ys else x::ys end
    val names = map stringSyntax.fromHOLstring strs |> all_distinct
    in names end
  fun get_DeclAssumExists () = !decl_exists
  fun cert_reset () =
    (decl_name := "";
     decl_abbrev := TRUTH;
     decl_term   := ``[]:dec list``;
     cert_memory := [];
     cenv_eq_thm := (DeclAssumCons_NIL |> GEN_ALL |> Q.SPEC `NONE`);
     decl_exists := (DeclAssumExists_NIL |> GEN_ALL |> Q.SPEC `NONE`);
     (* abbrev_counter := 0; *)
     abbrev_defs := [])
  fun map_cert_memory f = (cert_memory := map f (!cert_memory))
  fun get_names () = map (fn (n,_,_,_) => n) (!cert_memory)
  fun get_decl_name () = let
     val n = !decl_name
     in if n <> "" then n else
          let val c = current_theory() in (decl_name := c; c) end end
  fun get_DeclAssum () = ``DeclAssum ^(get_mn()) ^(!decl_term) env tys``
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
    val name = get_decl_name () ^ "_decls_" ^ int_to_string (!abbrev_counter)
    val _ = (abbrev_counter := 1 + (!abbrev_counter))
    val abbrev_def = new_definition(name,mk_eq(mk_var(name,``:decs``),rhs))
    val new_rw = REWRITE_RULE [abbrev_def |> GSYM]
    val _ = map_cert_memory (fn (n,tm,th,pre) => (n,tm,new_rw th,pre))
    val _ = (cenv_eq_thm := new_rw (!cenv_eq_thm))
    val _ = (decl_exists := new_rw (!decl_exists))
    val _ = (decl_term := (abbrev_def |> concl |> dest_eq |> fst))
    val _ = (abbrev_defs := abbrev_def::(!abbrev_defs))
    in () end
  fun finish_decl_abbreviation () = let
    fun expand_abbrevs [] = REFL (!decl_term)
      | expand_abbrevs [th] =
          (th |> CONV_RULE (RAND_CONV (REWR_CONV (SNOC_APPEND)))
           handle HOL_ERR _ => th)
      | expand_abbrevs (rw::rws) = let
          val th = expand_abbrevs rws
          in CONV_RULE ((RAND_CONV o RAND_CONV) (REWR_CONV th) THENC
                       RAND_CONV (REWR_CONV (SNOC_APPEND))) rw end
    val append_lemma = GSYM APPEND_ASSOC
    val append_nil = APPEND |> CONJUNCT1
    val append_cons = APPEND |> CONJUNCT2
    fun eval_append_conv tm = let
      val th = REWR_CONV append_cons tm
      in CONV_RULE ((RAND_CONV o RAND_CONV) eval_append_conv) th end
      handle HOL_ERR _ => (REWR_CONV append_nil ORELSEC ALL_CONV) tm
    val c = REPEATC
             (REWR_CONV append_lemma THENC
              RAND_CONV eval_append_conv) THENC
            eval_append_conv
    val lemma = expand_abbrevs (!abbrev_defs) |> CONV_RULE (RAND_CONV c)
    val rhs = lemma |> concl |> rand
    val name = get_decl_name () ^ "_decls"
    val abbrev_def = new_definition(name,mk_eq(mk_var(name,``:decs``),rhs))
    val new_rw = RW [lemma |> CONV_RULE (RAND_CONV (REWR_CONV (SYM abbrev_def)))]
    val _ = map_cert_memory (fn (n,tm,th,pre) => (n,tm,new_rw th,pre))
    val _ = (cenv_eq_thm := new_rw (!cenv_eq_thm))
    val _ = (decl_exists := new_rw (!decl_exists))
    val _ = (decl_term := (abbrev_def |> concl |> dest_eq |> fst))
    val _ = (decl_abbrev := abbrev_def)
    val strs = (!abbrev_defs) |> map (fst o dest_const o fst o dest_eq o concl)
    val _ = map (fn s => delete_const s handle NotFound => ()) strs
    in () end;
  (* functions for appending a new declaration *)
  val cs = listLib.list_compset()
  val () = computeLib.scrub_thms [LIST_TO_SET_THM,MEM,ALL_DISTINCT] cs
  val () = computeLib.add_thms [MEM,ALL_DISTINCT] cs
  val () = stringLib.add_string_compset cs
  val () = pairLib.add_pair_compset cs
  val () = computeLib.add_thms [evalPropsTheory.build_tdefs_cons] cs
  val eval = computeLib.CBV_CONV cs
  (* val previous_all_distinct = ref TRUTH *)
  fun snoc_cenv_eq_thm decl =
    if can (match_term ``(Dtype x) : dec``) decl then
      MATCH_MP (INST_mn DeclAssumCons_SNOC_Dtype) (!cenv_eq_thm)
      |> SPEC (decl |> rand)
      |> print_time "EVAL ALL_DISTINCT" (CONV_RULE ((RATOR_CONV o RAND_CONV) eval))
      |> print_time "EVAL2" (
         CONV_RULE (RAND_CONV EVAL THENC
                    (RATOR_CONV o RAND_CONV) EVAL))
      |> (fn th => (cenv_eq_thm := th; th))
    else if can (match_term ``(Dexn n l) : dec``) decl then
      MATCH_MP (INST_mn DeclAssumCons_SNOC_Dexn) (!cenv_eq_thm)
      |> SPEC (decl |> rator |> rand)
      |> SPEC (decl |> rand)
      |> print_time "EVAL ALL_DISTINCT" (CONV_RULE ((RATOR_CONV o RAND_CONV) eval))
      |> print_time "EVAL2" (
         CONV_RULE (RAND_CONV EVAL THENC
                    (RATOR_CONV o RAND_CONV) EVAL))
      |> (fn th => (cenv_eq_thm := th; th))
    else if can (match_term ``(Dlet v x) : dec``) decl then
      MATCH_MP (INST_mn DeclAssumCons_SNOC_Dlet) (!cenv_eq_thm)
      |> SPEC (rand (rand (rator decl))) |> SPEC (rand decl)
      |> (fn th => (cenv_eq_thm := th; th))
    else if can (match_term ``(Dletrec funs) : dec``) decl then
      MATCH_MP (INST_mn DeclAssumCons_SNOC_Dletrec) (!cenv_eq_thm)
      |> SPEC (rand decl)
      |> (fn th => (cenv_eq_thm := th; th))
    else
      failwith "snoc_cenv_eq_thm input is not recognised decl"
  fun snoc_decl decl = let
    val _ = print_time "snoc_cenv_eq_thm" snoc_cenv_eq_thm decl
    val _ = (decl_term := listSyntax.mk_snoc(decl,!decl_term))
    val f = if can (match_term ``(Dletrec funs) : dec``) decl then
              (fn (n:string,tm:term,th,pre) =>
                (n,tm,(MATCH_MP (INST_mn DeclAssum_Dletrec) th |> SPEC (rand decl)
                 |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) |> REWRITE_RULE [])
                 handle HOL_ERR _ => th,pre))
            else if can (match_term ``(Dlet v x) : dec``) decl then
              (fn (n:string,tm:term,th,pre) =>
                (n,tm,(MATCH_MP (INST_mn DeclAssum_Dlet) th
                 |> SPEC (rand (rand (rator decl))) |> SPEC (rand decl)
                 |> CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) |> REWRITE_RULE [])
                 handle HOL_ERR _ => th,pre))
            else if can (match_term ``(Dtype x) : dec``) decl then
              (fn (n:string,tm:term,th,pre) =>
                (n,tm,(th |> SPEC_ALL
                          |> Q.GEN `tys`
                          |> Q.GEN `env`
                          |> MATCH_MP (INST_mn DeclAssum_Dtype)
                          |> SPEC (rand decl)
                          |> SPEC_ALL
                          |> Q.GEN `env`)
                      handle HOL_ERR _ => th,pre))
            else if can (match_term ``(Dexn n l) : dec``) decl then
              (fn (n:string,tm:term,th,pre) =>
                (n,tm,(th |> SPEC_ALL
                          |> Q.GEN `tys`
                          |> Q.GEN `env`
                          |> MATCH_MP (INST_mn DeclAssum_Dexn)
                          |> SPEC (rator (rand decl))
                          |> SPEC (rand decl)
                          |> SPEC_ALL
                          |> Q.GEN `env`)
                      handle HOL_ERR _ => th,pre))
            else fail()
    val _ = print_time "map_cert_memory" map_cert_memory f
    in () end;
  fun snoc_dtype_decl dtype = let
    val decl = dtype
    val _ = let
      val th = MATCH_MP (INST_mn DeclAssumExists_SNOC_Dtype) (!decl_exists)
               |> SPEC (decl |> rand)
      val goal = th |> concl |> dest_imp |> fst
      val lemma = !cenv_eq_thm
      val tac =
        REPEAT STRIP_TAC
        THEN1 (SIMP_TAC std_ss [check_dup_ctors_def,LET_DEF,FOLDR] THEN EVAL_TAC)
        THEN1 EVAL_TAC
        THEN SIMP_TAC std_ss [type_defs_to_new_tdecs_def,MAP,
               DISJOINT_set_SIMP,mk_id_def]
        THEN (lemma |> RW1 [DeclAssumCons_def] |> SPEC_ALL
                    |> UNDISCH |> CONJUNCT1 |> ASSUME_TAC)
        THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
        THEN EVAL_TAC
      val lemma = auto_prove "snoc_dtype_decl" (goal,tac)
      val th = MY_MP "dtype" th lemma
      in decl_exists := th end
    val _ = snoc_decl decl
    val _ = update_decl_abbreviation ()
    in () end
  fun snoc_dexn_decl dexn = let
    val decl = dexn
    val _ = let
      val th = MATCH_MP (INST_mn DeclAssumExists_SNOC_Dexn) (!decl_exists)
               |> SPECL [(decl |> rator |> rand),(decl |> rand)]
      val goal = th |> concl |> dest_imp |> fst
      val lemma = !cenv_eq_thm
      val tac =
        NTAC 3 STRIP_TAC
        THEN ASSUME_TAC (lemma |> RW1 [DeclAssumCons_def] |> SPEC_ALL
                               |> UNDISCH |> CONJUNCT1)
        THEN ASM_REWRITE_TAC [] THEN EVAL_TAC
      val lemma = auto_prove "snoc_dexn_decl" (goal,tac)
      val th = MY_MP "dexn" th lemma
      in decl_exists := th end
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
  fun store_cert th pres decl_assum_x = let
    val decl_assum = (th |> hyp |> first
                        (can (match_term ``DeclAssum mn ds env tys``)))
    val decl = (decl_assum |> rator |> rator |> rand |> rator |> rand)
    val _ = snoc_decl decl
    val _ = let
      val th = MATCH_MP decl_assum_x (!decl_exists) |> SPEC_ALL
      val tm = th |> concl |> rand |> rator |> rand
      val i = fst (match_term tm decl)
      val th = INST i th
      in decl_exists := th end
    fun SMART_CONJUNCTS th =
      if aconv (concl th) T then [] else CONJUNCTS th
    fun SMART_LIST_CONJ [] = TRUTH
      | SMART_LIST_CONJ xs = LIST_CONJ xs
    val thms = th |> SMART_CONJUNCTS |> map UNDISCH_ALL
    val pres = pres
(*
val (th,pre) = hd ((zip thms pres))
*)
    fun process_thm (th,pre) = let
      val th = Q.GEN `env` (DISCH decl_assum th)
      val tm = concl (th |> SPEC_ALL |> UNDISCH_ALL)
      val const = tm |> rand |> rand
      val _ = is_const const orelse fail()
      val n = tm |> rator |> rand |> rand |> rand |> stringSyntax.fromHOLstring
      val _ = (cert_memory := (n,const,th,pre)::(!cert_memory))
      val _ = if concl pre = T then () else
                (print ("\nWARNING: " ^ n ^ " has a precondition.\n\n"))
      in () end;
    val _ = map process_thm (zip thms pres)
    val _ = update_decl_abbreviation ()
    val thms = take (length thms) (!cert_memory) |> rev
                 |> map (fn (_,_,th,pre) => th)
    in SMART_LIST_CONJ thms end
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
    val _ = if not pre_is_true then () else
              (print ("Precondition for " ^ fname ^ " proved.\n"))
    in new_pre end
  (* store/load to/from a single thm *)
  fun pack_certs () = let
    val _ = finish_decl_abbreviation ()
    in pack_5tuple
         (pack_list (pack_4tuple pack_string pack_term pack_thm pack_thm))
         pack_thm pack_term pack_thm pack_thm
           ((!cert_memory), (!decl_abbrev), (!decl_term),
            (!cenv_eq_thm), (!decl_exists)) end
  fun unpack_certs th = let
    val (cert,abbrev,t,cenv,ex) =
      unpack_5tuple
        (unpack_list (unpack_4tuple unpack_string unpack_term unpack_thm unpack_thm))
        unpack_thm unpack_term unpack_thm unpack_thm th
    val _ = (cert_memory := cert)
    val _ = (decl_abbrev := abbrev)
    val _ = (abbrev_defs := [abbrev])
    val _ = (decl_term := t)
    val _ = (cenv_eq_thm := cenv)
    val _ = (decl_exists := ex)
    in () end
end


(* code for managing type information *)

fun get_ty_case_const ty = let
  val th = TypeBase.case_def_of ty
  val case_const = th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                      |> concl |> dest_eq |> fst |> repeat rator
  in case_const end

fun name_of_type ty = let
  val case_const = get_ty_case_const ty
  val name = case_const |> dest_const |> fst |> explode |> rev
                        |> funpow 5 tl |> rev |> implode
  in name end;

val basic_theories =
   ["alist", "arithmetic", "bag", "bitstring", "bit", "bool",
    "combin", "container", "divides", "fcp", "finite_map", "float",
    "fmaptree", "frac", "gcdset", "gcd", "ind_type", "integer_word",
    "integer", "integral", "list", "llist", "marker", "measure",
    "numeral_bit", "numeral", "numpair", "numposrep", "num", "one",
    "operator", "option", "pair", "path", "patricia_casts",
    "patricia", "poly", "poset", "powser", "pred_set", "prelim",
    "prim_rec", "quote", "quotient_list", "quotient_option",
    "quotient_pair", "quotient_pred_set", "quotient_sum", "quotient",
    "rat", "real_sigma", "realax", "real", "relation", "res_quan",
    "rich_list", "ringNorm", "ring", "sat", "semi_ring", "seq",
    "set_relation", "sorting", "state_option", "state_transformer",
    "string_num", "string", "sum_num", "sum", "topology", "transc",
    "update", "util_prob", "while", "words"]

val use_full_type_names = ref true;

fun full_name_of_type ty =
  if !use_full_type_names then let
    val case_const = get_ty_case_const ty
    val thy_name = case_const |> dest_thy_const |> #Thy
    val thy_name = if mem thy_name basic_theories then "" else thy_name ^ "_"
    in thy_name ^ name_of_type ty end
  else name_of_type ty;

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
    if ty = ``:bool`` then ``Tapp [] TC_bool`` else
    if ty = ``:word8`` then ``Tapp [] TC_word8`` else
    if ty = ``:int`` then ``Tapp [] TC_int`` else
    if ty = ``:num`` then ``Tapp [] TC_int`` else
    if can dest_vartype ty then
      mk_comb(``Tvar``,stringSyntax.fromMLstring ((* string_tl *) (dest_vartype ty)))
    else let
      val (lhs,rhs) = find_type_mapping ty
      val i = match_type lhs ty
      val xs = free_typevars rhs
      val i = filter (fn {redex = a, residue = _} => mem a xs) i
      val tm = type2t rhs
      val s = map (fn {redex = a, residue = b} => type2t a |-> type2t b) i
      in subst s tm end handle HOL_ERR _ =>
    let
      val (x,tt) = dest_type ty
      val name = if x = "fun" then "fun" else
                 if x = "prod" then "prod" else
                   full_name_of_type ty
      val tt = map type2t tt
      val name_tm = stringSyntax.fromMLstring name
      val tt_list = listSyntax.mk_list(tt,type_of ``Tbool``)
      in if name = "fun"  then ``Tapp [^(el 1 tt);^(el 2 tt)] TC_fn`` else
         if name = "prod" then ``Tapp [^(el 1 tt);^(el 2 tt)] TC_tup`` else
         if name = "list" then ``Tapp ^tt_list (TC_name (Short ^name_tm))`` else
                               ``Tapp ^tt_list (TC_name (^(full_id name_tm)))`` end
  val vector_type_pat = ``:'a ml_translator$vector``
  fun dest_vector_type ty =
    if can (match_type vector_type_pat) ty then
      dest_type ty |> snd |> hd
    else failwith "not vector type"
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
    if ty = ``:unit`` then ``UNIT_TYPE`` else
    if ty = ``:bool`` then ``BOOL`` else
    if ty = ``:word8`` then ``WORD8`` else
    if ty = ``:num`` then ``NUM`` else
    if ty = ``:int`` then ``INT`` else
    if can dest_vector_type ty then let
      val inv = get_type_inv (dest_vector_type ty)
      in VECTOR_TYPE_def |> ISPEC inv |> SPEC_ALL
         |> concl |> dest_eq |> fst |> rator |> rator end
    else
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

fun get_unique_name str = let
  val names = get_names() @ ["o","+","-","*","div","mod","<",">","<=",">=","ref"]
  fun find_name str n = let
    val new_name = str ^ "_" ^ (int_to_string n)
    in if mem new_name names then find_name str (n+1) else new_name end
  fun find_new_name str =
    if mem str names then find_name str 1 else str
  val initial_name = clean_lowercase str
  val initial_name = if size initial_name = 0 then "f" else initial_name
  in find_new_name initial_name end

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


(* mapping from dec terms to SML *)

local
  val _ = computeLib.add_funs [tree_to_list_def,
                               tok_list_to_string_def,
                               tok_to_string_def,
                               ASCIInumbersTheory.n2s_def,
                               numposrepTheory.n2l_def,
                               ASCIInumbersTheory.HEX_def]
  fun dec2str sml d = let (* very slow at the moment *)
    val result =
      ``dec_to_sml_string ^d``
      |> EVAL |> concl |> rand |> stringSyntax.fromHOLstring
   (* |> (fn str => (print ("\n\n" ^ str ^ "\n\n"); str)) *)
      handle HOL_ERR _ => failwith("\nUnable to print "^(term_to_string d)^"\n\n")
    in result end;
in
  fun dec2str_sml d = dec2str true d
end


(* printing output e.g. SML syntax *)

val print_asts = ref false;

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
  fun print_decls () = if not (!print_asts) then () else let
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

fun check_uptodate_term tm =
  if Theory.uptodate_term tm then () else let
    val t = find_term (fn tm => is_const tm
      andalso not (Theory.uptodate_term tm)) tm
    val _ = print "\n\nFound out-of-date term: "
    val _ = print_term t
    val _ = print "\n\n"
    in () end

local
  val suffix = "_translator_state_thm"
  fun pack_state () = let
    val name = get_decl_name () ^ suffix
    val name_tm = stringSyntax.fromMLstring name
    val tag_lemma = ISPEC ``b:bool`` (ISPEC name_tm TAG_def) |> GSYM
    val p1 = pack_certs()
    val p2 = pack_types()
    val p = pack_pair I I (p1,p2)
    val th = PURE_ONCE_REWRITE_RULE [tag_lemma] p
    val _ = check_uptodate_term (concl th)
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
              "cakeML.ml_translator",
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
    handle HOL_ERR e => raise ERR "type_of_cases_const" (String.concat["For ",Parse.type_to_string ty,"\n",Feedback.format_ERR e])
  val ty = th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
              |> concl |> dest_eq |> fst |> repeat rator |> type_of
  in ty end

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

fun tag_name type_name const_name =
  if (type_name = "OPTION_TYPE") andalso (const_name = "NONE") then "NONE" else
  if (type_name = "OPTION_TYPE") andalso (const_name = "SOME") then "SOME" else
  if (type_name = "LIST_TYPE") andalso (const_name = "NIL") then "nil" else
  if (type_name = "LIST_TYPE") andalso (const_name = "CONS") then "::" else let
    val x = clean_lowercase type_name
    val y = clean_lowercase const_name
    fun upper_case_hd s =
      clean_uppercase (implode [hd (explode s)]) ^ implode (tl (explode s))
    val name = if y = "" then upper_case_hd x else upper_case_hd y
    val taken_names = get_cenv_names ()
    fun find_unique name n =
      if not (mem name taken_names) then name else
      if not (mem (name ^ "_" ^ int_to_string n) taken_names) then
        name ^ "_" ^ int_to_string n
      else find_unique name (n+1)
    in find_unique name 1 end;

val last_def_fail = ref T

fun derive_record_specific_thms ty = let
  val ty_name = name_of_type ty
  val access_funs =
    TypeBase.accessors_of ty
    |> map (rator o fst o dest_eq o concl o SPEC_ALL)
  val update_funs =
    TypeBase.updates_of ty
    |> map (rator o rator o fst o dest_eq o concl o SPEC_ALL)
  val thy_name = access_funs |> hd |>dest_thy_const |> #Thy
  val tm =
    DB.fetch thy_name (ty_name ^ "_11")
    |> SPEC_ALL |> concl |> dest_eq |> fst |> dest_eq |> fst
  val xs = dest_args tm
  val c = repeat rator tm
  val case_tm =
    DB.fetch thy_name (ty_name ^ "_case_cong")
    |> SPEC_ALL |> UNDISCH_ALL |> concl |> dest_eq |> fst |> repeat rator
  fun prove_accessor_eq (a,x) = let
    val v = mk_var("v",type_of tm)
    val f = foldr (fn (v,tm) => mk_abs(v,tm)) x xs
    val ty1 = case_tm |> type_of |> dest_type |> snd |> el 2
                                 |> dest_type |> snd |> hd
    val i = match_type ty1 (type_of f)
    val rhs = mk_comb(mk_comb(inst i case_tm,v),f)
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
    val ty1 = case_tm |> type_of |> dest_type |> snd |> el 2
                                 |> dest_type |> snd |> hd
    val i = match_type ty1 (type_of f)
    val rhs = mk_comb(mk_comb(inst i case_tm,v),f)
    val lhs = mk_comb(mk_comb(a,g),v)
    val goal = mk_forall(v,mk_forall(g,mk_eq(lhs,rhs)))
    val tac = Cases THEN SRW_TAC [] [DB.fetch thy_name (ty_name ^ "_fn_updates")]
    in prove(goal,tac) end
  val b_lemmas = map prove_updates_eq (zip update_funs xs)
  val arb = mk_arb(type_of tm)
  val tm2 = foldr (fn ((a,x),y) => mk_comb(``^a (K ^x)``,y)) arb (zip update_funs xs)
  val goal = mk_eq(tm2,tm)
  val rw_lemma = prove(goal,SRW_TAC []
    [DB.fetch thy_name (ty_name ^ "_component_equality")])
  val rw_lemmas = CONJ (DB.fetch thy_name (ty_name ^ "_fupdcanon")) rw_lemma
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

fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];

(*
  val ty = ``:'a + 'b``
  val tys = find_mutrec_types ty
*)

fun define_ref_inv is_exn_type tys = let
  val is_pair_type =
    (case tys of [ty] => can (match_type ty) ``:'a # 'b`` | _ => false)
  val is_list_type =
    (case tys of [ty] => can (match_type ty) ``:'a list`` | _ => false)
  val is_option_type =
    (case tys of [ty] => can (match_type ty) ``:'a option`` | _ => false)
  fun get_name ty = clean_uppercase (full_name_of_type ty) ^ "_TYPE"
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
    val ml_ty_name = full_name_of_type ty
    val def_name = mk_var(name,list_mk_type (ss @ [input]) ``:v -> bool``)
    val lhs = foldl (fn (x,y) => mk_comb(y,x)) def_name (ss @ [input,``v:v``])
    in (ml_ty_name,xs,ty,lhs,input) end
  val ys = map mk_lhs all
  fun reg_type (_,_,ty,lhs,_) = new_type_inv ty (rator (rator lhs));
  val _ = map reg_type ys
  val rw_lemmas = CONJ (list_lemma ()) (pair_lemma ())
  val def_tm = let
    fun mk_lines ml_ty_name lhs ty [] input = []
      | mk_lines ml_ty_name lhs ty (x::xs) input = let
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
      val str_ty_name = stringLib.fromMLstring
            (if is_exn_type then tag else ml_ty_name)
      val vs = listSyntax.mk_list(map (fn (_,z) => z) vars,``:v``)
      val tyi = if is_exn_type then ``TypeExn`` else ``TypeId``
      val tag_tm = if is_pair_type then ``NONE:(tvarN # tid_or_exn) option``
                   else if is_list_type orelse is_option_type then
                     ``(SOME (^str, TypeId (Short ^str_ty_name)))``
                   else ``(SOME (^str, ^tyi (^(full_id str_ty_name))))``
      val tm = mk_conj(``v = Conv ^tag_tm ^vs``,tm)
      val tm = list_mk_exists (map (fn (_,z) => z) vars, tm)
      val tm = subst [input |-> x] (mk_eq(lhs,tm))
      (* val vs = filter (fn x => x <> def_name) (free_vars tm) *)
      val ws = free_vars x
      in tm :: mk_lines ml_ty_name lhs ty xs input end
    val zs = Lib.flatten (map (fn (ml_ty_name,xs,ty,lhs,input) =>
               mk_lines ml_ty_name lhs ty xs input) ys)
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
     \\ IMP_RES_TAC v_size_lemmas \\ TRY DECIDE_TAC
     \\ TRY (Q.PAT_ASSUM `MEM x xs` (fn th =>
              ASSUME_TAC th THEN Induct_on [ANTIQUOTE (rand (rand (concl th)))]))
     \\ FULL_SIMP_TAC std_ss [MEM,FORALL_PROD,size_def] \\ REPEAT STRIP_TAC
     \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC)
(*
  Define [ANTIQUOTE def_tm]
*)
  val inv_def = if is_list_type then LIST_TYPE_def else
                  tDefine name [ANTIQUOTE def_tm] tac
  val inv_def = CONV_RULE (DEPTH_CONV ETA_CONV) inv_def
  val inv_def = REWRITE_RULE [GSYM rw_lemmas] inv_def
  val _ = save_thm(name ^ "_def",inv_def)
  val ind = fetch "-" (name ^ "_ind") handle HOL_ERR _ => TypeBase.induction_of (hd tys)
(*
  val inv_def = tDefine name [ANTIQUOTE def_tm] ALL_TAC
*)
  fun has_arg_with_type ty line =
    ((line |> SPEC_ALL |> concl |> dest_eq |> fst |> rator |> rand |> type_of) = ty)
  val inv_defs = map (fn ty => (ty,LIST_CONJ (filter (has_arg_with_type ty)
                                     (CONJUNCTS inv_def)))) tys
  (* register the new type invariants *)
  fun sub lhs th = subst [(lhs |> repeat rator) |->
    (th |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
        |> concl |> dest_eq |> fst |> repeat rator)] lhs
  val ys2 = map (fn ((_,th),(ml_ty_name,xs,ty,lhs,input)) =>
                   (ml_ty_name,xs,ty,sub lhs th,input)) (zip inv_defs ys)
  val _ = map reg_type ys2
  (* equality type -- TODO: make this work for mutrec *)
  val eq_lemmas = let
    val tm = inv_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                     |> concl |> dest_eq |> fst |> rator |> rator
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
    val eq_lemma = auto_prove "EqualityType" (goal,
      REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [EqualityType_def]
      \\ STRIP_TAC THEN1
       (REPEAT (Q.PAT_ASSUM `!x1 x2 x3 x4. bbb` (K ALL_TAC))
        \\ (Induct ORELSE Cases)
        \\ SIMP_TAC (srw_ss()) [inv_def,no_closures_def,PULL_EXISTS]
        \\ REPEAT STRIP_TAC \\ RES_TAC)
      \\ STRIP_TAC
      THEN1
       (REPEAT (Q.PAT_ASSUM `!x1 x2. bbb ==> bbbb` (K ALL_TAC))
        \\ (Induct ORELSE Cases)
        \\ SIMP_TAC (srw_ss()) [inv_def,no_closures_def,PULL_EXISTS]
        \\ Cases_on `x2` \\ SIMP_TAC (srw_ss()) [inv_def,no_closures_def,PULL_EXISTS]
        \\ REPEAT STRIP_TAC \\ METIS_TAC [])
      THEN1
       (REPEAT (Q.PAT_ASSUM `!x1 x2. bbb ==> bbbb` (K ALL_TAC))
        \\ (Induct ORELSE Cases)
        \\ SIMP_TAC (srw_ss()) [inv_def,no_closures_def,PULL_EXISTS]
        \\ TRY (Cases_on `x2`)
        \\ SIMP_TAC (srw_ss()) [inv_def,no_closures_def,PULL_EXISTS, types_match_def]
        \\ REPEAT STRIP_TAC \\ METIS_TAC []))
    (* check that the result does not mention itself *)
    val (tm1,tm2) = dest_imp goal
    val _ = not (can (find_term (fn t => t = rand tm2)) tm1) orelse fail()
    in [eq_lemma] end handle HOL_ERR _ => map (K TRUTH) tys
  val res = map (fn ((th,inv_def),eq_lemma) => (th,inv_def,eq_lemma))
                (zip inv_defs eq_lemmas)
  in (name,res) end;

fun domain ty = ty |> dest_fun_type |> fst
fun codomain ty = ty |> dest_fun_type |> snd

fun persistent_skip_case_const const = let
  val ty = (domain (type_of const))
  fun thy_name_to_string thy name =
    if thy = current_theory() then name else thy ^ "Theory." ^ name
  val thm_name = if ty = ``:bool`` then "COND_DEF" else
    DB.match [] (concl (TypeBase.case_def_of ty))
    |> map (fn ((thy,name),_) => thy_name_to_string thy name) |> hd
  val str = thm_name
  val str = "(Drule.CONJUNCTS " ^ str ^ ")"
  val str = "(List.hd " ^ str ^ ")"
  val str = "(Drule.SPEC_ALL " ^ str ^ ")"
  val str = "(Thm.concl " ^ str ^ ")"
  val str = "(boolSyntax.dest_eq " ^ str ^ ")"
  val str = "(Lib.fst " ^ str ^ ")"
  val str = "(Lib.repeat Term.rator " ^ str ^ ")"
  val str = "val () = computeLib.set_skip computeLib.the_compset" ^
            " " ^ str ^ " (SOME 1);\n"
  val _ = adjoin_to_theory
     {sig_ps = NONE, struct_ps = SOME(fn ppstrm => PP.add_string ppstrm str)}
  in computeLib.set_skip computeLib.the_compset const (SOME 1) end

val _ = persistent_skip_case_const ``COND:bool -> 'a -> 'a -> 'a``;

 val (FILTER_ASSUM_TAC : (term -> bool) -> tactic) = let
  fun sing f [x] = f x
    | sing f _ = raise ERR "sing" "Bind Error"
  fun add_assum (x,th) = UNDISCH (DISCH x th)
  fun f p (asl,w) =
    ([(filter p asl,w)], sing (fn th =>
           (foldr add_assum th (filter (not o p) asl))))
  in f end

(*
val ty = ``:'a list``; derive_thms_for_type false ty
val ty = ``:'a # 'b``; derive_thms_for_type false ty
val ty = ``:'a + num``; derive_thms_for_type false ty
val ty = ``:num option``; derive_thms_for_type false ty

val _ = Datatype `exn = A num num | B int`;
val ty = ``:exn``;
val is_exn_type = true;

val ty = ``:unit``; derive_thms_for_type false ty
*)

fun derive_thms_for_type is_exn_type ty = let
  val (ty,ret_ty) = dest_fun_type (type_of_cases_const ty)
  val is_record = 0 < length(TypeBase.fields_of ty)
  val tys = find_mutrec_types ty
  val is_pair_type =
    (case tys of [ty] => can (match_type ty) ``:'a # 'b`` | _ => false)
  val is_list_type =
    (case tys of [ty] => can (match_type ty) ``:'a list`` | _ => false)
  val is_option_type =
    (case tys of [ty] => can (match_type ty) ``:'a option`` | _ => false)
  val _ = map (fn ty => print ("Adding type " ^ type_to_string ty ^ "\n")) tys
  (* look up case theorems *)
  val case_thms = map (fn ty => (ty, get_nchotomy_of ty)) tys
  (* define coupling invariant for data refinement and prove EqualityType lemmas *)
  val (name,inv_defs) = define_ref_inv is_exn_type tys
  val _ = map (fn (_,inv_def,_) => print_inv_def inv_def) inv_defs
  fun list_mk_type [] ret_ty = ret_ty
    | list_mk_type (x::xs) ret_ty = mk_type("fun",[type_of x,list_mk_type xs ret_ty])
  (* define a CakeML datatype declaration *)
  val (dtype,dtype_list) =
    if name = "PAIR_TYPE" then (``Dtype []``,``[]:'a list``) else let
    fun extract_dtype_part th = let
      val xs = CONJUNCTS th |> map (dest_eq o concl o SPEC_ALL)
      val ys = xs |>  map (fn (x,y) => (x |> rator |> rand,
                                        y |> list_dest dest_exists |> last
                                          |> list_dest dest_conj |> hd
                                          |> rand |> rator |> rand |> rand))
      val tyname = ys |> hd |> snd |> rand |> rand |> rand
      val ys = map (fn (x,y) => (y |> rator |> rand,
                                 x |> dest_args |> map (type2t o type_of))) ys
      fun mk_line (x,y) = pairSyntax.mk_pair(x,
                           listSyntax.mk_list(y,type_of ``Tbool``))
      val lines = listSyntax.mk_list(map mk_line ys,``:tvarN # t list``)
      fun string_tl s = s |> explode |> tl |> implode
      val ts = th |> concl |> list_dest dest_conj |> hd
                  |> list_dest dest_forall |> last |> dest_eq |> fst
                  |> rator |> rand |> type_of |> dest_type |> snd
                  |> map (stringSyntax.fromMLstring o (* string_tl o *) dest_vartype)
      val ts_tm = listSyntax.mk_list(ts,``:string``)
      val dtype = ``(^ts_tm,^tyname,^lines)``
      in dtype end
    val dtype_parts = inv_defs |> map #2 |> map extract_dtype_part
    val dtype_list = listSyntax.mk_list(dtype_parts,type_of (hd dtype_parts))
    in (``(Dtype ^dtype_list): dec``,dtype_list) end
  val dexn_list = if not is_exn_type then [] else let
    val xs = dtype |> rand |> rator |> rand |> rand |> rand
                   |> listSyntax.dest_list |> fst
                   |> map pairSyntax.dest_pair
    in map (fn (n,l) => ``Dexn ^n ^l``) xs end
  (* cons assumption *)
  fun smart_full_id tyname =
    if is_list_type orelse is_option_type orelse is_pair_type
    then ``Short ^tyname`` else full_id tyname
  fun make_assum tyname c = let
    val (x1,x2) = dest_pair c
    val l = x2 |> listSyntax.dest_list |> fst |> length |> numSyntax.term_of_int
    val tyi = if is_exn_type then ``TypeExn`` else ``TypeId``
    val name = if is_exn_type then full_id x1 else smart_full_id tyname
    in ``lookup_cons ^x1 env = SOME (^l,^tyi ^name)`` end
  val type_assum =
      dtype_list
      |> listSyntax.dest_list |> fst
      |> map (list_dest dest_pair)
      |> map (fn xs => (el 2 xs, el 3 xs |> listSyntax.dest_list |> fst))
      |> map (fn (tyname,conses) => map (make_assum tyname) conses)
      |> flatten |> list_mk_conj
      handle HOL_ERR _ => T
(*
  val ((ty,case_th),(_,inv_def,eq_lemma)) = hd (zip case_thms inv_defs)
  val inv_lhs = inv_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                        |> concl |> dest_eq |> fst
  val x = inv_lhs |> rator |> rand
  val input = mk_var("input",type_of x)
  val inv_lhs = subst [x|->input] inv_lhs
*)
  (* prove lemma for case_of *)
  fun prove_case_of_lemma (ty,case_th,inv_lhs,inv_def) = let
    val cases_th = TypeBase.case_def_of ty
    val (x1,x2) = cases_th |> CONJUNCTS |> hd |> concl |> repeat (snd o dest_forall)
                           |> dest_eq
    val case_const = x1 |> repeat rator
    (* val _ = persistent_skip_case_const case_const *)
    val ty1 = case_const |> type_of |> domain
    val ty2 = x2 |> type_of
    val cases_th = INST_TYPE [ty2 |-> ``:'return_type``] cases_th
                   |> INST_TYPE (match_type ty1 ty)
    fun replace_match_exp f tm = let
      val (x,y) = dest_comb tm
      in if is_const x then mk_comb(x,f y) else mk_comb(replace_match_exp f x,y) end
    val cases_tm =
      cases_th |> CONJUNCTS |> hd |> concl |> repeat (snd o dest_forall)
               |> dest_eq |> fst |> replace_match_exp (fn tm => mk_arb (type_of tm))
    fun rename [] = []
      | rename (x::xs) = let val k = "f" ^ int_to_string (length xs + 1)
                         in (x,mk_var(k,type_of x)) :: rename xs end
    val vs = rev (rename (free_vars cases_tm))
    val cases_tm = subst (map (fn (x,y) => x |-> y) vs) cases_tm
    val exp = cases_tm |> replace_match_exp (fn tm => mk_var ("x",type_of tm))
    val input_var = filter (fn x => not (mem x (free_vars cases_tm))) (free_vars exp) |> hd
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
      val tag_tm = if name = "PAIR_TYPE"
                   then ``NONE:tvarN id option``
                   else ``(SOME (Short ^str))``
      in ``(Pcon ^tag_tm ^vars, ^exp)`` end) ts
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
      val env = mk_var("env",``:all_env``)
      val env = foldr (fn ((x,n,v),y) => ``write ^n ^v ^y``) env (rev xs)
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
    val goal = mk_imp(type_assum,mk_imp(tt,mk_imp(hyps,result)))
    val evaluate_Mat =
      ``evaluate c x env (Mat e pats) (xx,Rval res)``
      |> (ONCE_REWRITE_CONV [evaluate_cases] THENC SIMP_CONV (srw_ss()) [])
    val evaluate_match_Conv =
      ``evaluate_match c x env args
           ((Pcon xx pats,exp2)::pats2) errv (yyy,Rval y)``
      |> (ONCE_REWRITE_CONV [evaluate_cases] THENC
          SIMP_CONV (srw_ss()) [pmatch_def])
    val evaluate_match_rw = prove(
      ``evaluate_match c (menv,cenv,env) (e1,e2) args
          ((Pcon xx pats,exp2)::pats2) errv (yyy,Rval y) <=>
        ALL_DISTINCT (pat_bindings (Pcon xx pats) []) /\
        case pmatch cenv e2 (Pcon xx pats) args env of
        | No_match =>
            evaluate_match c (menv,cenv,env) (e1,e2) args pats2 errv (yyy,Rval y)
        | Match env7 =>
            evaluate c (menv,cenv,env7) (e1,e2) exp2 (yyy,Rval y)
        | _ => F``,
      SIMP_TAC std_ss [evaluate_match_Conv
        |> Q.INST [`x`|->`(menv,cenv,e)`,`env`|->`(e1,e2)`]
        |> Q.INST [`e`|->`env`]
        |> SIMP_RULE std_ss []]
      \\ Cases_on `pmatch cenv e2 (Pcon xx pats) args env`
      \\ FULL_SIMP_TAC (srw_ss()) []);
    val IF_T = prove(``(if T then x else y) = x:'a``,SIMP_TAC std_ss []);
    val IF_F = prove(``(if F then x else y) = y:'a``,SIMP_TAC std_ss []);
    fun print_tac s g = (print s; ALL_TAC g)
    val _ = print "Case translation:"
    val init_tac =
          REWRITE_TAC [CONTAINER_def]
          \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `x` case_th)
    fun case_tac n =
          print_tac (" " ^ int_to_string n)
          \\ FILTER_ASSUM_TAC (fn tm =>
               not (can (match_term ``TAG (n:num) (b:bool)``) tm) orelse
               can (match_term ``TAG (0:num) (b:bool)``) tm orelse
               can (match_term ``TAG ^(numSyntax.term_of_int n) (b:bool)``) tm)
          \\ POP_ASSUM (fn th => FULL_SIMP_TAC (srw_ss()) [th])
          \\ Q.PAT_ASSUM `TAG 0 bbb` (MP_TAC o
               (CONV_RULE ((RAND_CONV o RAND_CONV) (ALPHA_CONV ``v:v``))) o
               REWRITE_RULE [TAG_def,Eval_def])
          \\ POP_ASSUM (MP_TAC o REWRITE_RULE [] o remove_primes o
                        SPEC_ALL o REWRITE_RULE [TAG_def])
          \\ STRIP_TAC \\ STRIP_TAC
          \\ POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [inv_def] o UNDISCH)
          \\ Q.PAT_ASSUM `TAG n bbb` (STRIP_ASSUME_TAC o UNDISCH_ALL o
                REWRITE_RULE [GSYM AND_IMP_INTRO] o remove_primes o
                SPEC_ALL o REWRITE_RULE [TAG_def,Eval_def])
          \\ CONV_TAC (REWR_CONV Eval_def) \\ Q.EXISTS_TAC `res`
          \\ ASM_REWRITE_TAC [evaluate_Mat]
          \\ Q.LIST_EXISTS_TAC [`v`,`0,empty_store`] \\ ASM_REWRITE_TAC []
          \\ PairCases_on `env`
          \\ FULL_SIMP_TAC (srw_ss()) [pmatch_def,pat_bindings_def,
                  lookup_cons_def,same_tid_def,id_to_n_def,
                  same_ctor_def,write_def]
          \\ NTAC n
            (ONCE_REWRITE_TAC [evaluate_match_rw]
             \\ ASM_SIMP_TAC (srw_ss()) [pat_bindings_def,pmatch_def,
                  same_ctor_def,same_tid_def,id_to_n_def,write_def])
    val tac = init_tac THENL (map (fn (n,f,fxs,pxs,tm,exp,xs) => case_tac n) ts)
(*
val n = 1
val n = 2
val _ = set_goal([],goal)
*)
    val case_lemma = auto_prove "case-of-proof" (goal,tac)
    val case_lemma = case_lemma |> PURE_REWRITE_RULE [TAG_def]
    val _ = print " done.\n"
    in (case_lemma,ts) end;

(*
val (n,f,fxs,pxs,tm,exp,xs) = hd ts
*)
  (* prove lemmas for constructors *)
  fun derive_cons ty inv_lhs inv_def (n,f,fxs,pxs,tm,exp,xs) = let
    val pat = tm
    fun str_tl s = implode (tl (explode s))
    val exps = map (fn (x,_,_) => (x,mk_var("exp" ^ str_tl (fst (dest_var x)), ``: exp``))) xs
    val tag = tag_name name (repeat rator tm |> dest_const |> fst)
    val str = stringLib.fromMLstring tag
    val exps_tm = listSyntax.mk_list(map snd exps,``:exp``)
    val inv = inv_lhs |> rator |> rator
    val tag_name = if name = "PAIR_TYPE"
                   then ``NONE:tvarN id option``
                   else ``(SOME (Short ^str))``
    val result = ``Eval env (Con ^tag_name ^exps_tm) (^inv ^tm)``
    fun find_inv tm =
      if type_of tm = ty then (mk_comb(rator (rator inv_lhs),tm)) else
        (mk_comb(get_type_inv (type_of tm),tm))
    val tms = map (fn (x,exp) => ``Eval env ^exp ^(find_inv x)``) exps
    val tm = if tms = [] then T else list_mk_conj tms
    val cons_assum = type_assum
                     |> list_dest dest_conj
                     |> filter (fn tm => aconv
                           (tm |> rator |> rand |> rator |> rand) str)
                     |> list_mk_conj
                     handle HOL_ERR _ => T
    val goal = mk_imp(cons_assum,mk_imp(tm,result))
    fun add_primes str 0 = []
      | add_primes str n = mk_var(str,``:v``) :: add_primes (str ^ "'") (n-1)
    val witness = listSyntax.mk_list(add_primes "res" (length xs),``:v``)
    val lemma = prove(goal,
      SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
      \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) [PULL_EXISTS]
      \\ PairCases_on `env`
      \\ FULL_SIMP_TAC (srw_ss()) [inv_def,evaluate_list_SIMP,do_con_check_def,
           all_env_to_cenv_def,lookup_cons_def,build_conv_def,id_to_n_def]
      \\ EXISTS_TAC witness \\ FULL_SIMP_TAC std_ss [CONS_11,evaluate_list_SIMP])
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
    val conses = print_time "conses" (map (derive_cons ty inv_lhs inv_def)) ts
    in (ty,eq_lemma,inv_def,conses,case_lemma,ts) end
  val res = map make_calls (zip case_thms inv_defs)
(*
  val dexn = hd dexn_list
*)
  val _ = if mem name ["LIST_TYPE","OPTION_TYPE","PAIR_TYPE"]
          then ()
          else if not is_exn_type
               then print_time "snoc_dtype_decl" snoc_dtype_decl dtype
               else (map snoc_dexn_decl dexn_list; ())
  val (rws1,rws2) = if not is_record then ([],[])
                    else derive_record_specific_thms (hd tys)
  in (rws1,rws2,res) end;

local
  val translator = ref (fn th => I (th:thm))
  fun do_translate th = (!translator) th
  fun add_type ty = let
    val (rws1,rws2,res) = derive_thms_for_type false ty
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
  fun register_exn_type ty = let
    val (rws1,rws2,res) = derive_thms_for_type true ty
    val _ = add_type_thms (rws1,rws2,res)
    val _ = map do_translate rws1
    in res end
end

fun register_term_types tm = let
  fun every_term f tm =
    ((if is_abs tm then every_term f (snd (dest_abs tm))
      else if is_comb tm then (every_term f (rand tm); every_term f (rator tm))
      else ()); f tm)
  val special_types = [``:num``,``:int``,``:bool``,``:word8``,``:unit``,``:char``]
                      @ get_user_supplied_types ()
  fun ignore_type ty =
    if can (first (fn ty1 => can (match_type ty1) ty)) special_types then true else
    if not (can dest_type ty) then true else
    if can (dest_fun_type) ty then true else false
  fun typeops ty = let
    val (tname,targs) = dest_type ty
    in ty :: flatten (map typeops targs) end
    handle HOL_ERR _ => []
  fun register_term_type tm = let
    val tys = typeops (type_of tm) |> filter (not o ignore_type)
    val _ = map register_type tys
    in () end
  in every_term register_term_type tm end;

(* tests:
register_type ``:'a list``;
register_type ``:'a # 'b``;
register_type ``:'a + num``;
register_type ``:num option``;
register_type ``:unit``;
*)

fun inst_cons_thm tm hol2deep = let
  val th = cons_for tm |> UNDISCH
  val res = th |> UNDISCH_ALL |> concl |> rand |> rand
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val xs = args res
  val ss = fst (match_term res tm)
  val ys = map (fn x => hol2deep (subst ss x)) xs
  val th1 = if length ys = 0 then TRUTH else LIST_CONJ ys
  in MATCH_MP th (UNDISCH_ALL th1)
     handle HOL_ERR _ => raise UnableToTranslate tm end

fun inst_case_thm_for tm = let
  val (_,_,names) = TypeBase.dest_case tm
  val names = map fst names
  val th = case_of ((repeat rator tm) |> type_of |> domain) |> UNDISCH
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
  val tm = hyps
  val tm = y
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
    val env = mk_var("env",``:all_env``)
    val lemma = INST [env|->new_env] lemma
                |> PURE_REWRITE_RULE [lookup_cons_write]
    val (x1,x2) = dest_conj x handle HOL_ERR _ => (T,x)
    val (z1,z2) = dest_imp (concl lemma)
    val thz =
      QCONV (SIMP_CONV std_ss [ASSUME x1,Eval_Var_SIMP,
               lookup_var_write] THENC
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
  val th = th |> UNDISCH_ALL
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
  val lemma = (* auto_prove "single_line_def-1" *) prove(goal,
    SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,GSYM rw]
    \\ REPEAT STRIP_TAC
    \\ CONV_TAC (BINOP_CONV (REWR_CONV (GSYM CONTAINER_def)))
    \\ SRW_TAC [] []
    \\ BasicProvers.EVERY_CASE_TAC
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
  val _ = Pmatch.with_classic_heuristic quietDefine [ANTIQUOTE def_tm]
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
           |> concl |> rand |> rand
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
  val lemma = (* auto_prove "single_line_def-2" *) prove(goal,
    SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD,TRUE_def,FALSE_def] \\ SRW_TAC [] []
    \\ BasicProvers.EVERY_CASE_TAC
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
  val def' = CONV_RULE (RAND_CONV (REWRITE_CONV [UNCURRY_SIMP] THENC
               (DEPTH_CONV PairRules.PBETA_CONV))) def
  in if concl def' = T then def else def' end

fun is_rec_def def = let
  val thms = def |> SPEC_ALL |> CONJUNCTS |> map SPEC_ALL
  val const = hd thms |> concl |> dest_eq |> fst |> repeat rator
  val rhss = thms |> map (snd o dest_eq o concl)
  in can (first (can (find_term (fn tm => tm = const)))) rhss end

fun is_NONE NONE = true | is_NONE _ = false

local
  val preferred = ref ([]:string list);
in
  fun add_preferred_thy thy_name = (preferred := thy_name::(!preferred))
  fun fetch_from_thy thy name = let
    fun aux [] name = failwith ("cannot find theorem: " ^ name)
      | aux (thy::ts) name = fetch thy name handle HOL_ERR _ => aux ts name
    in aux ((!preferred) @ [thy]) name end
end

fun find_ind_thm def = let
  val const = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL |> concl
                  |> dest_eq |> fst |> repeat rator
  val r = dest_thy_const const
  val ind = fetch_from_thy (#Thy r) ((#Name r) ^ "_ind")
            handle HOL_ERR _ =>
            fetch_from_thy (#Thy r) ((#Name r) ^ "_IND")
            handle HOL_ERR _ =>
            fetch_from_thy (#Thy r) ("ConstMult_ind")
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

fun mk_fun_type ty1 ty2 = mk_type("fun",[ty1,ty2])

fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

fun all_distinct [] = []
  | all_distinct (x::xs) = let
      val ys = all_distinct xs
      in if mem x ys then ys else x::ys end

fun get_induction_for_def def = let
  val res = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                |> concl |> dest_eq |> fst |> repeat rator
                |> dest_thy_const
  in fetch_from_thy (#Thy res) ((#Name res) ^ "_ind") handle HOL_ERR _ =>
     fetch_from_thy (#Thy res) ((#Name res) ^ "_IND") end
  handle HOL_ERR _ => let
  fun mk_arg_vars xs = let
    fun aux [] = []
      | aux (x::xs) = mk_var("v" ^ (int_to_string (length xs + 1)),type_of x)
                       :: aux xs
    in (rev o aux o rev) xs end
  fun dest_fun_app tm = let
    val (x,y) = dest_comb tm
    val (f,args) = dest_fun_app x
    in (f,args @ [y]) end handle HOL_ERR _ => (tm,[])
  fun f tm = let
    val (lhs,rhs) = dest_eq tm
    val (const,args) = dest_fun_app lhs
    val vargs = mk_arg_vars args
    val args = pairSyntax.list_mk_pair args
    in (const,vargs,args,rhs) end
  val cs = def |> CONJUNCTS |> map (f o concl o SPEC_ALL)
  val cnames = map (fn (x,_,_,_) => x) cs |> all_distinct
  val cs = map (fn c => (c, map (fn (x,y,z,q) => (y,z,q))
                              (filter (fn (x,_,_,_) => c = x) cs))) cnames
           |> map (fn (c,x) => (c,hd (map (fn (x,y,z) => x) x),
                                map (fn (x,y,z) => (y,z)) x))
  fun split_at P [] = fail()
    | split_at P (x::xs) = if P x then ([],x,xs) else let
        val (x1,y1,z1) = split_at P xs
        in (x::x1,y1,z1) end
  fun find_pat_match (_,args,pats) = let
    val pat = hd pats |> fst
    val vs = pairSyntax.list_mk_pair args
    val ss = fst (match_term vs pat)
    val xs = map (subst ss) args
    in (split_at (not o is_var) xs) end
  val xs = map find_pat_match cs
  val ty = map (fn (_,x,_) => type_of x) xs |> hd
  val raw_ind = TypeBase.induction_of ty
  fun my_mk_var ty = mk_var("pat_var", ty)
  val index = ref 0
  fun goal_step (xs,t,ys) = let
    val v = my_mk_var (type_of t)
    val args = xs @ [v] @ ys
    val P = mk_var("P" ^ (int_to_string (!index)) ,
              list_mk_fun_type ((map type_of args) @ [``:bool``]))
    val _ = (index := (!index) + 1)
    val prop = list_mk_comb(P,args)
    val goal = list_mk_forall(args,prop)
    val step = mk_abs(v,list_mk_forall(xs @ ys,prop))
    in (P,(goal,step)) end
  val res = map goal_step xs
  fun ISPEC_LIST [] th = th
    | ISPEC_LIST (x::xs) th = ISPEC_LIST xs (ISPEC x th)
  val ind = ISPEC_LIST (map (snd o snd) res) raw_ind
            |> CONV_RULE (DEPTH_CONV BETA_CONV)
  val goal1 = ind |> concl |> dest_imp |> snd
  val goal2 = list_mk_conj (map (fst o snd) res)
  val goal = mk_imp(goal1,goal2)
  val lemma = prove(goal, REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [])
  val ind = MP lemma (ind |> UNDISCH_ALL) |> DISCH_ALL
            |> GENL (map fst res)
  in ind end handle HOL_ERR _ =>
  failwith "unable to construct induction theorem from TypeBase info"

fun mutual_to_single_line_def def = let
  (* get induction theorem *)
  val ind = get_induction_for_def def
  (* collapse to one line per function *)
  fun mk_arg_vars xs = let
    fun aux [] = []
      | aux (x::xs) = mk_var("v" ^ (int_to_string (length xs + 1)),type_of x)
                       :: aux xs
    in (rev o aux o rev) xs end
  fun dest_fun_app tm = let
    val (x,y) = dest_comb tm
    val (f,args) = dest_fun_app x
    in (f,args @ [y]) end handle HOL_ERR _ => (tm,[])
  fun f tm = let
    val (lhs,rhs) = dest_eq tm
    val (const,args) = dest_fun_app lhs
    val vargs = mk_arg_vars args
    in (const,vargs,args,rhs) end
  val cs = def |> CONJUNCTS |> map (f o concl o SPEC_ALL)
  val cnames = map (fn (x,_,_,_) => x) cs |> all_distinct
  (* val _ = 1 < length cnames orelse failwith "not mutually recursive" *)
  val cs = map (fn c => (c, map (fn (x,y,z,q) => (y,z,q))
                              (filter (fn (x,_,_,_) => c = x) cs))) cnames
           |> map (fn (c,x) => (c,hd (map (fn (x,y,z) => x) x),
                                map (fn (x,y,z) => (y,z)) x))
  fun goal_line (c,_,[(args,body)]) = let
        val gg = mk_eq(list_mk_comb(c,args),body)
        in (list_mk_abs(args,gg),gg) end
    | goal_line (c,args,pats) = let
    fun transpose [] = []
      | transpose ([]::xs) = []
      | transpose xs = map hd xs :: transpose (map tl xs)
    val us = transpose (map fst pats) |> map all_distinct
    val ts = zip us args |> map (fn (x,y) => length x > 1)
    val pats = map (fn (ps,body) =>
      (pairSyntax.list_mk_pair (map snd (filter fst (zip ts ps))),body)) pats
    val rhs = TypeBase.mk_pattern_fn pats
    val rhs_x = filter fst (zip ts args) |> map snd |> pairSyntax.list_mk_pair
    val rhs = mk_comb(rhs,rhs_x)
    val ss = filter (not o fst) (zip ts (zip us args)) |> map snd
             |> map (fn (x,y) => y |-> hd x)
    val args = map (subst ss) args
    val gg = mk_eq(list_mk_comb(c,args),rhs)
    in (list_mk_abs(args,gg),gg) end
  val gs = map goal_line cs
  val target = map snd gs |> list_mk_conj
  in if concl def = target then (def |> CONJUNCTS,SOME ind) else let
  val goals = map fst gs
  val lemma = SPECL goals ind
  val goal = lemma |> concl |> dest_imp |> fst
  val _ = not (can (find_term is_arb) goal) orelse failwith "requires precondition"
  val lemma1 = prove(goal,
    REPEAT STRIP_TAC THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN CONV_TAC (RATOR_CONV (PURE_ONCE_REWRITE_CONV [def]))
    THEN SIMP_TAC (srw_ss()) [])
  val def2 = MP lemma lemma1
             |> CONV_RULE (DEPTH_CONV BETA_CONV)
             |> CONJUNCTS |> map SPEC_ALL
  in (def2,SOME ind) end end handle HOL_ERR _ => let
  val (def,ind) = single_line_def def
  in ([def],ind) end

val AUTO_ETA_EXPAND_CONV = let (* ``K ($=) --> K (\x y. x = y)`` *)
  val expand_ops = [``($+):num->num->num``, ``($-):num->num->num``,
    ``($*):num->num->num``, ``($DIV):num->num->num``,
    ``($MOD):num->num->num``, ``($+):int->int->int``,
    ``($-):int->int->int``, ``($*):int->int->int``]
  val eq_const = ``($=):'a->'a->bool``
  fun must_eta_expand tm =
    TypeBase.is_constructor tm orelse
    mem tm expand_ops orelse can (match_term eq_const) tm
  fun full_arg_num tm = let
    fun n ty = n (snd (dest_fun_type ty)) + 1 handle HOL_ERR _ => 0
    in n (type_of tm) end
  fun FULL_ETA_CONV tm = let
    val v = genvar (fst (dest_fun_type (type_of tm)))
    val lemma = ETA_CONV (mk_abs(v,mk_comb(tm,v)))
    in ((K (SYM lemma)) THENC ABS_CONV (FULL_ETA_CONV)) tm end
    handle HOL_ERR _ => ALL_CONV tm
  fun aux n tm =
    if is_const tm then
      if n < full_arg_num tm andalso must_eta_expand tm
      then FULL_ETA_CONV tm
      else ALL_CONV tm
    else if is_comb tm then let
      val (f,x) = dest_comb tm
      in (RATOR_CONV (aux (n+1)) THENC RAND_CONV (aux 0)) tm end
    else if is_abs tm then let
      val (v,body) = dest_abs tm
      in (ABS_CONV (aux 0)) tm end
    else if is_var tm then ALL_CONV tm
    else fail()
  in aux 0 end

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

val use_mem_intro = ref false;

fun preprocess_def def = let
  val def = force_eqns def
  val is_rec = is_rec_def def
  val (defs,ind) = mutual_to_single_line_def def
  fun rephrase_def def = let
    val def = RW1 [GSYM TRUE_def, GSYM FALSE_def] def
    val def = remove_pair_abs def |> SPEC_ALL
    val def = rename_bound_vars_rule " variable " (GEN_ALL def) |> SPEC_ALL
    val def = CONV_RULE (DEPTH_CONV split_let_and_conv) def
    val def = if def |> SPEC_ALL |> concl |> dest_eq |> fst |> is_const
              then SPEC_ALL (RW1 [FUN_EQ_THM] def) else def
    val def = PURE_REWRITE_RULE ([ADD1,boolTheory.literal_case_DEF,
                num_case_thm] @ get_preprocessor_rws()) def
    val def = CONV_RULE (AUTO_ETA_EXPAND_CONV THENC REDEPTH_CONV BETA_CONV) def
    val def = rename_bound_vars_rule "v" (GEN_ALL def) |> SPEC_ALL
    in def end;
  val defs = map rephrase_def defs
  val ind = if is_rec andalso is_NONE ind then SOME (find_ind_thm (hd defs)) else ind
  fun option_apply f NONE = NONE | option_apply f (SOME x) = SOME (f x)
  val mem_intro_rule = PURE_REWRITE_RULE [MEMBER_INTRO]
  val (defs,ind) = if not (!use_mem_intro) then (defs,ind) else
                     (map mem_intro_rule defs, option_apply mem_intro_rule ind)
  in (is_rec,defs,ind) end;


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
  val assum = ``Eval env (Var (Short ^str)) (^inv ^v)``
  val new_env = ``write ^str (v:v) env``
  val old_env = new_env |> rand
  val c = SIMP_CONV bool_ss [Eval_Var_SIMP,lookup_var_write]
          THENC DEPTH_CONV stringLib.string_EQ_CONV
          THENC REWRITE_CONV []
  val c = (RATOR_CONV o RAND_CONV) c THENC
          (RAND_CONV o RATOR_CONV o RAND_CONV) c
  val c1 = ((RATOR_CONV o RAND_CONV) (REWRITE_CONV [ASSUME assum]))
  val th = thx |> D |> CONV_RULE c1 |> DISCH assum
               |> INST [old_env|->new_env]
               |> PURE_REWRITE_RULE [lookup_cons_write]
               |> CONV_RULE c
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

(*
  val (v,x) = dest_abs tm
  val th = hol2deep x
  val th = inst_Eval_env v th
*)

fun apply_Eval_Fun v th fix = let
  val th1 = inst_Eval_env v th
  val th2 = if fix then MATCH_MP Eval_Fun_Eq (GEN ``v:v`` th1)
                   else MATCH_MP Eval_Fun (GEN ``v:v`` (FORCE_GEN v th1))
  in th2 end;

fun apply_Eval_Recclosure recc fname v th = let
  val vname = fst (dest_var v)
  val vname_str = stringLib.fromMLstring vname
  val fname_str = stringLib.fromMLstring fname
  val FORALL_CONV = RAND_CONV o ABS_CONV
  val lemma = SPECL [recc,fname_str] Eval_Recclosure_ALT
              |> CONV_RULE ((FORALL_CONV o FORALL_CONV o
                             RATOR_CONV o RAND_CONV) EVAL)
  val pat = lemma |> concl |> find_term (can
               (match_term ``find_recfun name (funs:('a,'b # 'c) alist)``))
  val lemma = SIMP_RULE std_ss [EVAL pat] lemma
  val inv = get_type_inv (type_of v)
  val pat = lemma |> concl |> find_term (can (match_term ``Eval env``))
  val new_env = pat |> rand
  val old_env = ``env:all_env``
  val assum = subst [old_env|->new_env]
                ``Eval env (Var (Short ^vname_str)) (^inv ^v)``
  val thx = th |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum (* |> SIMP_RULE bool_ss [] *)
               |> INST [old_env|->new_env]
               |> PURE_REWRITE_RULE [Eval_Var_SIMP,
                                     lookup_var_write,lookup_cons_write]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> REWRITE_RULE [SafeVar_def]
  val new_assum = fst (dest_imp (concl thx))
  val th1 = thx |> UNDISCH |> REWRITE_RULE [ASSUME new_assum]
                |> UNDISCH_ALL
                |> CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV v))
                |> DISCH new_assum
  val th2 = MATCH_MP lemma (Q.INST [`env`|->`cl_env`] (GEN ``v:v`` th1))
  val assum = ASSUME (fst (dest_imp (concl th2)))
  val th3 = D th2 |> REWRITE_RULE [assum]
                  |> REWRITE_RULE [Eval_Var_SIMP,
                       lookup_var_write,FOLDR,write_rec_thm]
                  |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
                  |> REWRITE_RULE [Eval_Var_SIMP,lookup_var_write,FOLDR]
                  |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
                  |> REWRITE_RULE [SafeVar_def]
  val lemma = Eval_Eq_Recclosure |> UNDISCH
  val lemma_lhs = lemma |> concl |> dest_eq |> fst
  fun replace_conv tm = let
    val (i,t) = match_term lemma_lhs tm
    val th9 = INST i (INST_TYPE t lemma)
    val name = lemma_lhs |> inst t |> subst i |> rand |> rand
    in INST [``name:string``|->name] th9 end handle HOL_ERR _ => NO_CONV tm
  val th4 = CONV_RULE (QCONV (DEPTH_CONV replace_conv)) th3
  in th4 end

fun clean_assumptions th4 = let
  (* lift cl_env assumptions out *)
  val env = mk_var("env",``:all_env``)
  val pattern = ``DeclAssum mn ds ^env tys``
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
  val rec_patterns = ref ([]:(term * string) list);
in
  fun install_rec_pattern lhs fname =
    (rec_patterns := (lhs,fname)::(!rec_patterns); get_pre_var lhs fname)
  fun uninstall_rec_patterns () = (rec_patterns := [])
  fun match_rec_pattern tm = let
    val pats = (!rec_patterns)
    val (lhs,fname) = first (fn (pat,fname) => can (match_term pat) tm) pats
    in (lhs,fname,get_pre_var lhs fname) end
  fun get_rec_patterns () = (!rec_patterns)
end

val check_inv_fail = ref T;

fun check_inv name tm result = let
  val tm2 = result |> concl |> rand |> rand
  in if aconv tm2 tm then result else let
    val _ = (check_inv_fail := tm)
    val _ = (show_types_verbosely := true)
    val _ = print ("\n\nhol2deep failed at '" ^ name ^ "'\n\ntarget:\n\n")
    val _ = print_term tm
    val _ = print "\n\nbut derived:\n\n"
    val _ = print_term tm2
    val _ = print "\n\n\n"
    val _ = (show_types_verbosely := false)
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
  val lemma = mk_thm([],``!b x. Eq b x = (b:'a->v->bool)``)
  val tm2 = QCONV (REWRITE_CONV [lemma]) res |> concl |> dest_eq |> snd
  in tm2 end

val MAP_pattern = ``MAP (f:'a->'b)``
val FILTER_pattern = ``FILTER (f:'a->bool)``
val EVERY_pattern = ``EVERY (f:'a->bool)``
val EXISTS_pattern = ``EXISTS (f:'a->bool)``
val is_precond = can (match_term ``PRECONDITION b``)

val IF_TAKEN = prove(
  ``!b x y. b ==> ((if b then x else y) = x:'unlikely)``, SIMP_TAC std_ss []);

local
  val ty = ``:word8``
in
  fun is_word8_literal tm =
    if type_of tm = ty
    then numSyntax.is_numeral (rand tm)
    else false
end

val Num_ABS_pat = Eval_Num_ABS |> concl |> rand |> rand |> rand

val int_of_num_pat = Eval_int_of_num |> concl |> rand |> rand |> rand
val int_of_num_o_pat = Eval_int_of_num_o |> concl |> rand |> rand |> rand
val o_int_of_num_pat = Eval_o_int_of_num |> concl |> rand |> rand |> rand

val vec_vec_pat = Eval_vector |> SPEC_ALL |> RW [AND_IMP_INTRO]
  |> concl |> dest_imp |> snd |> rand |> rand
val vec_sub_pat = Eval_sub |> SPEC_ALL |> RW [AND_IMP_INTRO]
  |> concl |> dest_imp |> snd |> rand |> rand
val vec_len_pat = Eval_length |> SPEC_ALL |> RW [AND_IMP_INTRO]
  |> concl |> dest_imp |> snd |> rand |> rand

(*
val tm = rhs
*)

fun hol2deep tm =
  (* variables *)
  if is_var tm then let
    val (name,ty) = dest_var tm
    val inv = get_type_inv ty
    val str = stringSyntax.fromMLstring name
    val result = ASSUME (mk_comb(``Eval env (Var (Short ^str))``,mk_comb(inv,tm)))
    in check_inv "var" tm result end else
  (* constants *)
  if tm = oneSyntax.one_tm then Eval_Val_UNIT else
  if numSyntax.is_numeral tm then SPEC tm Eval_Val_NUM else
  if intSyntax.is_int_literal tm then SPEC tm Eval_Val_INT else
  if is_word8_literal tm then
    SPEC (tm |> rand) Eval_Val_WORD8 |> SIMP_RULE std_ss [] else
  if stringSyntax.is_char_literal tm then SPEC tm Eval_Val_CHAR else
  if (tm = T) orelse (tm = F) then SPEC tm Eval_Val_BOOL else
  if (tm = ``TRUE``) orelse (tm = ``FALSE``) then SPEC tm Eval_Val_BOOL else
  (* data-type constructor *)
  inst_cons_thm tm hol2deep handle HOL_ERR _ =>
  (* data-type pattern-matching *)
  inst_case_thm tm hol2deep handle HOL_ERR _ =>
  (* recursive pattern *)
  if can match_rec_pattern tm then let
    val (lhs,fname,pre_var) = match_rec_pattern tm
    fun dest_args tm = rand tm :: dest_args (rator tm) handle HOL_ERR _ => []
    val xs = dest_args tm
    val f = repeat rator lhs
    val str = stringLib.fromMLstring fname
    fun mk_fix tm = let
      val inv = get_type_inv (type_of tm)
      in ``Eq ^inv ^tm`` end
    fun mk_arrow x y = ``Arrow ^x ^y``
    fun mk_inv [] res = res
      | mk_inv (x::xs) res = mk_inv xs (mk_arrow (mk_fix x) res)
    val inv = mk_inv xs (get_type_inv (type_of tm))
    val ss = fst (match_term lhs tm)
    val pre = subst ss pre_var
    val h = ASSUME ``PreImp ^pre (Eval env (Var (Short ^str)) (^inv ^f))``
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
  if is_cond tm then
    if is_precond (tm |> rator |> rator |> rand) then let
      val (x1,x2,x3) = dest_cond tm
      val th2 = hol2deep x2
      val lemma = IF_TAKEN |> SPEC x1 |> ISPEC x2 |> SPEC x3 |> UNDISCH |> SYM
      val result = th2 |> CONV_RULE ((RAND_CONV o RAND_CONV) (K lemma))
      in check_inv "if" tm result end
    else let
      val (x1,x2,x3) = dest_cond tm
      val th1 = hol2deep x1
      val th2 = hol2deep x2
      val th3 = hol2deep x3
      val th = MATCH_MP Eval_If (LIST_CONJ [D th1, D th2, D th3])
      val result = UNDISCH th
      in check_inv "if" tm result end else
  (* Num (ABS i) *)
  if can (match_term Num_ABS_pat) tm then let
    val x1 = tm |> rand |> rand
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_Num_ABS th1
    in check_inv "num_abs" tm result end else
  (* w2n *)
  if wordsSyntax.is_w2n tm andalso (type_of (rand tm) = ``:word8``) then let
    val x1 = tm |> rand
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_w2n th1
    in check_inv "w2n" tm result end else
  (* &n *)
  if can (match_term int_of_num_pat) tm then let
    val x1 = tm |> rand
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_int_of_num th1
    in check_inv "int_of_num" tm result end else
  (* $& o f *)
  if can (match_term int_of_num_o_pat) tm then let
    val x1 = tm |> rand
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_int_of_num_o th1
    in check_inv "int_of_num_o" tm result end else
  (* f o $& *)
  if can (match_term o_int_of_num_pat) tm then let
    val x1 = tm |> rator |> rand
    val th1 = hol2deep x1
    val result = MATCH_MP Eval_o_int_of_num th1
    in check_inv "o_int_of_num" tm result end else
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
    fun pat_match pat tm = (match_term pat tm; rator pat)
    val r = pat_match MAP_pattern tm handle HOL_ERR _ =>
            pat_match EVERY_pattern tm handle HOL_ERR _ =>
         (* pat_match EXISTS_pattern tm handle HOL_ERR _ =>
            pat_match FILTER_pattern tm handle HOL_ERR _ => *) fail()
    val (m,f) = dest_comb tm
    val th_m = hol2deep r
    val (v,x) = dest_abs f
    val th_f = hol2deep x
    val th_f = apply_Eval_Fun v th_f true
    val thi = th_f |> DISCH_ALL |> RW [AND_IMP_INTRO] |> GEN v
    val thi = HO_MATCH_MP Eq_IMP_And thi
    val thi = MATCH_MP (MATCH_MP Eval_Arrow th_m) thi
    val list_type_def = LIST_CONJ [
      EVAL ``LIST_TYPE (a:('a -> v -> bool)) [] v``,
      EVAL ``LIST_TYPE (a:('a -> v -> bool)) (x::xs) v``]
    val LIST_TYPE_And = prove(
      ``LIST_TYPE (And a P) = And (LIST_TYPE a) (EVERY (P:'a->bool))``,
      SIMP_TAC std_ss [FUN_EQ_THM,And_def] \\ Induct
      \\ FULL_SIMP_TAC std_ss [MEM,list_type_def]
      \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [And_def])
    val thi = RW [LIST_TYPE_And] thi
    val EVERY_MEM_CONTAINER = prove(
      ``!P l. EVERY P l <=> !e. CONTAINER (MEM e l) ==> P (e:'a)``,
      SIMP_TAC std_ss [EVERY_MEM,CONTAINER_def]);
    val thi = MATCH_MP And_IMP_Eq thi
    val thi = SIMP_RULE std_ss [EVERY_MEM_CONTAINER] thi
    val result = thi |> UNDISCH_ALL
    in check_inv "map" tm result end handle HOL_ERR _ =>
  (* vectors *)
  if can (match_term vec_vec_pat) tm then let
    val th1 = hol2deep (rand tm)
    val result = MATCH_MP Eval_vector th1
    in check_inv "vec_vec" tm result end else
  if can (match_term vec_sub_pat) tm then let
    val th1 = hol2deep (rand (rator tm))
    val th2 = hol2deep (rand tm)
    val result = MATCH_MP Eval_sub th1
    val result = MATCH_MP result th2
    val result = result |> UNDISCH
    in check_inv "vec_sub" tm result end else
  if can (match_term vec_len_pat) tm then let
    val th1 = hol2deep (rand tm)
    val result = MATCH_MP Eval_length th1
    in check_inv "vec_len" tm result end else
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
    val goal = ``PRECONDITION F ==> Eval env (Raise (Con(SOME(Short"Bind"))[])) (^inv ^tm)``
    val result = prove(goal,SIMP_TAC std_ss [PRECONDITION_def]) |> UNDISCH
    in check_inv "arb" tm result end
  else raise (UnableToTranslate tm)

fun hol2val tm = let
  val th_rhs = hol2deep tm
  val res = mk_comb(rand (concl th_rhs),mk_var("v",``:v``))
            |> EVAL |> SIMP_RULE std_ss [] |> concl |> rand |> rand
  in res end;

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

fun every [] = true
  | every (x::xs) = x andalso every xs

fun clean_precondition pre_def = let
  val th = SIMP_RULE (srw_ss()) [] pre_def
  val th = REWRITE_RULE [CONTAINER_def] th
  val th = rename_bound_vars_rule "v" (GEN_ALL th) |> SPEC_ALL
  in th end;

fun ex_rename_bound_vars_rule th = let
  val i = ref 0
  fun next_name () = (i:= !i+1; "x" ^ int_to_string (!i))
  fun next_var v = mk_var(next_name (), type_of v)
  fun next_alpha_conv tm = let
    val (v,_) = dest_abs tm
    val _ = not (String.isPrefix "x" (fst (dest_var v))) orelse fail()
    in ALPHA_CONV (next_var v) tm end handle HOL_ERR _ => NO_CONV tm
  in CONV_RULE (DEPTH_CONV next_alpha_conv) th end

fun extract_precondition_non_rec th pre_var =
  if not (is_imp (concl th)) then (th,NONE) else let
    val c = (REWRITE_CONV [CONTAINER_def,PRECONDITION_def] THENC
             ONCE_REWRITE_CONV [GSYM PRECONDITION_def] THENC
             SIMP_CONV (srw_ss()) [FALSE_def,TRUE_def])
    val c = (RATOR_CONV o RAND_CONV) c
    val th = CONV_RULE c th
    val rhs = th |> concl |> dest_imp |> fst |> rand
    in if rhs = T then
      (UNDISCH_ALL (SIMP_RULE std_ss [EVAL ``PRECONDITION T``] th),NONE)
    else let
(*
    in if free_vars rhs = [] then
      (UNDISCH_ALL (SIMP_RULE std_ss [EVAL ``PRECONDITION T``] th),NONE)
    else let
*)
    val def_tm = mk_eq(pre_var,rhs)
    val pre_def = quietDefine [ANTIQUOTE def_tm]
    val c = REWR_CONV (GSYM pre_def)
    val c = (RATOR_CONV o RAND_CONV o RAND_CONV) c
    val th = CONV_RULE c th |> UNDISCH_ALL
    val pre_def = clean_precondition pre_def
    in (th,SOME pre_def) end end

val IMP_PreImp_LEMMA = prove(
  ``!b1 b2 b3. (b1 ==> b3 ==> b2) ==> b3 ==> PreImp b1 b2``,
  REPEAT Cases THEN REWRITE_TAC [PreImp_def,PRECONDITION_def]);

local
  val PRE_IMP = prove(``T /\ PRECONDITION b ==> PRECONDITION b``,EVAL_TAC)
  val PreImp_IMP = prove(``PreImp b1 b2 /\ T ==> PreImp b1 b2``,EVAL_TAC)
  val CONJ_IMP = prove(
    ``!b1 b2 b12 b3 b4 b34.
        (b1 /\ b2 ==> b12) /\ (b3 /\ b4 ==> b34) ==>
        ((b1 /\ b3) /\ (b2 /\ b4) ==> b12 /\ b34)``,
      REPEAT Cases THEN EVAL_TAC) |> SPEC_ALL;
  val IMP_SPLIT = prove(
    ``!b12 b3 b4 b34.
        (b12 = b12) /\ (b3 /\ b4 ==> b34) ==>
        ((b12 ==> b3) /\ (b12 ==> b4) ==> (b12 ==> b34))``,
    REPEAT Cases THEN EVAL_TAC) |> SPEC_ALL;
  val FORALL_SPLIT = prove(
    ``(!x. P1 x /\ P2 x ==> P (x:'a)) ==>
      ($! P1 ) /\ ($! P2 ) ==> $! P ``,
    FULL_SIMP_TAC std_ss [FORALL_THM]);
  val DEFAULT_IMP = prove(``!b1. b1 /\ b1 ==> b1``,SIMP_TAC std_ss []);
in
  fun derive_split tm =
    if can (match_term (PRE_IMP |> concl |> rand)) tm then let
      val m = fst (match_term (PRE_IMP |> concl |> rand) tm)
      in INST m PRE_IMP end else
    if can (match_term (PreImp_IMP |> concl |> rand)) tm then let
      val m = fst (match_term (PreImp_IMP |> concl |> rand) tm)
      in INST m PreImp_IMP end else
    if is_conj tm then let
      val (x1,x2) = dest_conj tm
      in MATCH_MP CONJ_IMP (CONJ (derive_split x1) (derive_split x2)) end else
    if is_imp tm then let
      val (x1,x2) = dest_imp tm
      val th1 = REFL x1
      val th2 = derive_split x2
      in MATCH_MP IMP_SPLIT (CONJ th1 th2) end else
    if is_forall tm then let
      val (v,body) = dest_forall tm
      val th = derive_split body
      val th = CONV_RULE (RAND_CONV (UNBETA_CONV v) THENC
                 (RATOR_CONV o RAND_CONV) (BINOP_CONV (UNBETA_CONV v))) th
      in MATCH_MP FORALL_SPLIT (GEN v th) end else
    SPEC tm DEFAULT_IMP
end

fun extract_precondition_rec thms = let
  fun rephrase_pre (fname,def,th) = let
    val (lhs,_) = dest_eq (concl def)
    val pre_var = get_pre_var lhs fname
    val th = SIMP_RULE bool_ss [CONTAINER_NOT_ZERO] th
    val th = ex_rename_bound_vars_rule th
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
               (REWRITE_CONV [GSYM AND_IMP_INTRO])) th
    val tm = concl th |> dest_imp |> fst
    val rw1 = ASSUME ``!b. PRECONDITION b = T``
    val tm1 = QCONV (REWRITE_CONV [rw1]) tm |> concl |> rand
    val pat = Eval_def |> SPEC_ALL |> concl |> dest_eq |> fst
    val rw2 = ASSUME (list_mk_forall(free_vars pat,pat))
    val tm2 = QCONV (REWRITE_CONV [rw2,PreImp_def]) tm |> concl |> rand
    in (fname,def,th,pre_var,tm1,tm2,rw2) end
  val thms = map rephrase_pre thms
(*
val (fname,def,th) = hd thms
*)
  (* check whether the precondition is T *)
  fun get_subst (fname,def,th,pre_var,tm1,tm2,rw2) = let
    val pre_v = repeat rator pre_var
    val true_pre = list_mk_abs ((dest_args pre_var), T)
    in pre_v |-> true_pre end
  val ss = map get_subst thms
  fun is_true_pre (fname,def,th,pre_var,tm1,tm2,rw2) =
    ((tm2 |> subst ss
          |> QCONV (REWRITE_CONV [rw2,PreImp_def,PRECONDITION_def,CONTAINER_def])
          |> concl |> rand) = T)
  val no_pre = every (map is_true_pre thms)
  (* if no pre then remove pre_var from thms *)
  in if no_pre then let
    fun remove_pre_var (fname,def,th,pre_var,tm1,tm2,rw2) = let
      val th5 = INST ss th
                |> SIMP_RULE bool_ss [PRECONDITION_EQ_CONTAINER]
                |> PURE_REWRITE_RULE [PreImp_def,PRECONDITION_def]
                |> CONV_RULE (DEPTH_CONV BETA_CONV THENC
                                (RATOR_CONV o RAND_CONV) (REWRITE_CONV []))
      in (fname,def,th5,NONE) end
    in map remove_pre_var thms end else let
  val combine_lemma = prove(
    ``!b1 b2 b3 b4. (b1 /\ b2 ==> b3) /\ (b3 ==> b4) ==> b2 ==> b1 ==> b4``,
    REPEAT Cases THEN SIMP_TAC std_ss [])

(*
  val (fname,def,th,pre_var,tm1,tm2,rw2) = hd thms
*)
  fun separate_pre (fname,def,th,pre_var,tm1,tm2,rw2) = let
    val lemma = derive_split (th |> concl |> dest_imp |> fst)
    val lemma = MATCH_MP combine_lemma (CONJ lemma th)
                |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                     (PURE_REWRITE_CONV [PRECONDITION_def]))
    in (fname,def,lemma,pre_var) end;
  val thms2 = map separate_pre thms
  fun diff [] ys = []
    | diff (x::xs) ys = if mem x ys then diff xs ys else x :: diff xs ys
  val all_pre_vars = map (fn (fname,def,lemma,pre_var) =>
                            repeat rator pre_var) thms2
(*
val (fname,def,lemma,pre_var) = hd thms2
*)
  val all_pres = map (fn (fname,def,lemma,pre_var) => let
    val tm = lemma |> concl |> dest_imp |> fst
    val vs = diff (free_vars tm) all_pre_vars
    in list_mk_forall(vs,mk_imp(tm,pre_var)) end) thms2
    |> list_mk_conj
  val (_,_,pre_def) = Hol_reln [ANTIQUOTE all_pres]
  val clean_pre_def = pre_def |> PURE_REWRITE_RULE [CONTAINER_def]
  val name = clean_pre_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
               |> concl |> dest_eq |> fst |> repeat rator |> dest_const |> fst
  val _ = delete_binding (name ^ "_rules") handle NotFound => ()
  val _ = delete_binding (name ^ "_ind") handle NotFound => ()
  val _ = delete_binding (name ^ "_strongind") handle NotFound => ()
  val _ = delete_binding (name ^ "_cases") handle NotFound => ()
  val _ = save_thm(name ^ "_def", clean_pre_def)
  val pre_defs = pre_def |> CONJUNCTS |> map SPEC_ALL
  val thms3 = zip pre_defs thms2
  fun get_sub (pre,(fname,def,lemma,pre_var)) = let
    val x = pre_var |> repeat rator
    val y = pre |> concl |> dest_eq |> fst |> repeat rator
    in x |-> y end
  val ss = map get_sub thms3
(*
val (pre,(fname,def,lemma,pre_var)) = hd thms3
*)
  fun compact_pre (pre,(fname,def,lemma,pre_var)) = let
    val c = (RATOR_CONV o RAND_CONV) (REWR_CONV (SYM pre))
    val lemma = lemma |> INST ss |> CONV_RULE c
                      |> MATCH_MP IMP_PreImp_LEMMA
    val pre = pre |> PURE_REWRITE_RULE [CONTAINER_def]
    in (fname,def,lemma,SOME pre) end
  val thms4 = map compact_pre thms3
  in thms4 end end


(* main translation routines *)

fun get_info def = let
  val (lhs,rhs) = dest_eq (concl def)
  val fname = repeat rator lhs |> dest_const |> fst |> get_unique_name
  in (fname,lhs,rhs,def) end;

fun comma [] = ""
  | comma [x] = x
  | comma (x::xs) = x ^ ", " ^ comma xs

fun all_distinct [] = []
  | all_distinct (x::xs) =
      if mem x xs then all_distinct xs else x :: all_distinct xs

fun remove_Eq th = let
  val pat = ``Arrow (Eq a (x:'a)) (b:'b->v->bool)``
  fun dest_EqArrows tm =
    if can (match_term pat) tm
    then (rand o rand o rator) tm :: dest_EqArrows (rand tm)
    else []
  val rev_params = th |> concl |> rand |> rator |> dest_EqArrows |> rev
  fun f (v,th) =
    HO_MATCH_MP Eval_FUN_FORALL (GEN v th) |> SIMP_RULE std_ss [FUN_QUANT_SIMP]
  in foldr f th rev_params end handle HOL_ERR _ => th

fun rev_param_list tm =
  if is_comb tm then rand tm :: rev_param_list (rator tm) else []

val EVAL_T_F = LIST_CONJ [EVAL ``CONTAINER TRUE``, EVAL ``CONTAINER FALSE``]

fun reset_translation () =
  (cert_reset(); type_reset(); print_reset(); finalise_reset());

fun abbrev_code (fname,def,th,v) = let
  val th = th |> UNDISCH_ALL
  val exp = th |> concl |> rator |> rand
  val n = "[[ " ^ fname ^ "_code ]]"
  val code_def = new_definition(n,mk_eq(mk_var(n,type_of exp),exp))
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (K (GSYM code_def))) th
  in (code_def,(fname,def,th,v)) end

val find_def_for_const =
  ref ((fn const => raise UnableToTranslate const) : term -> thm);

val IMP_PreImp_THM = prove(
  ``(b ==> PreImp x y) ==> ((x ==> b) ==> PreImp x y)``,
  Cases_on `b` \\ FULL_SIMP_TAC std_ss [PreImp_def,PRECONDITION_def]);

val PreImp_IMP = prove(
  ``(PRECONDITION x ==> PreImp x y) ==> PreImp x y``,
  SIMP_TAC std_ss [PreImp_def]);

fun force_thm_the (SOME x) = x | force_thm_the NONE = TRUTH

local
  val lookup_cons_pat = ``lookup_cons cname env = SOME x``
  val imp_lemma = prove(``!f. (f x = y) ==> !z. (f x = f z) ==> ((f:'a->'b) z = y)``,
                        REPEAT STRIP_TAC THEN FULL_SIMP_TAC bool_ss []) |> SPEC_ALL
in
  fun clean_lookup_cons th = let
    val tms = find_terms (can (match_term lookup_cons_pat)) (concl th)
              |> all_distinct
    in if length tms = 0 then th else let
    val lemmas = MATCH_MP (INST_mn DeclAssumCons_cons_lookup) (get_cenv_eq_thm ())
                 |> CONV_RULE (REWRITE_CONV [EVERY_DEF] THENC
                               DEPTH_CONV PairRules.PBETA_CONV)
                 |> SPEC_ALL |> UNDISCH |> CONJUNCTS
    fun in_term_list [] t = false
      | in_term_list (tm::tms) t = aconv t tm orelse in_term_list tms t
    val rwt = filter (in_term_list tms o concl) lemmas
                    |> map (Q.INST [`env`|->`shaddow_env`])
                    |> map (UNDISCH o Q.SPEC `env` o MATCH_MP imp_lemma)
                    |> LIST_CONJ
    val th = th |> RW [rwt] |> D
    in th end end
end

local
  val cs = listLib.list_compset()
  val () = computeLib.scrub_thms [LIST_TO_SET_THM,MEM,ALL_DISTINCT] cs
  val () = computeLib.add_thms [MEM,ALL_DISTINCT] cs
  val () = stringLib.add_string_compset cs
  val () = combinLib.add_combin_compset cs
  val () = pairLib.add_pair_compset cs
  val eval = computeLib.CBV_CONV cs

  val cs2 = listLib.list_compset()
  val () = computeLib.scrub_thms [LIST_TO_SET_THM,MEM,ALL_DISTINCT] cs2
  val () = computeLib.add_thms [MEM,ALL_DISTINCT] cs2
  val () = stringLib.add_string_compset cs2
  val () = combinLib.add_combin_compset cs2
  val () = optionLib.OPTION_rws cs2
  val () = computeLib.add_thms [initSemEnvTheory.prim_sem_env_eq] cs2
  val () = computeLib.add_datatype_info cs2 (valOf(TypeBase.fetch``:sem_environment``))
  val eval2 = computeLib.CBV_CONV cs2
in
  fun finalise_module_translation () = let
    fun DISCH_DeclAssum lemma = let
      val th = lemma |> DISCH_ALL
                     |> PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]
                     |> UNDISCH_ALL
      val pattern = ``DeclAssum mn ds env tys``
      val x = hyp th |> filter (can (match_term pattern)) |> hd
              handle Empty => get_DeclAssum ()
      in DISCH x th end
    val _ = finalise_translation ()
    val ex = get_DeclAssumExists ()
    val th = MATCH_MP DeclAssumExists_SOME_IMP_Tmod ex |> SPEC_ALL
    val tm = th |> concl |> dest_imp |> fst
    val lemma = auto_prove "ALL_DISTINCT type_names" (tm,
      ONCE_REWRITE_TAC [case get_decl_abbrev () of SOME x => x | NONE => TRUTH]
      \\ PURE_REWRITE_TAC [type_names_def] \\ CONV_TAC eval)
    val th = MP th lemma
    val th1 = CONJUNCT1 th
    val th2 = CONJUNCT2 th
    fun expand lemma = let
      val th3 = MATCH_MP (DISCH_DeclAssum lemma) (MATCH_MP DeclEnv ex)
      val th3 = MATCH_MP Eval_Var_Short_merge (th3 |> RW [th2])
                |> CONV_RULE ((RATOR_CONV o RAND_CONV) eval2)
      in MP th3 TRUTH |> DISCH_ALL |> GEN_ALL end
      handle HOL_ERR _ => TRUTH;
    val xs = (map (fst o get_cert) (rev (get_names ())))
    val th4 = LIST_CONJ (map expand xs) |> RW []
    in CONJ th1 th4 |> GEN_ALL end
end

(*

translate def

val def = Define `fac n = if n = 0 then 1 else fac (n-1) * (n:num)`;
val def = Define `foo n = if n = 0 then 1 else foo (n-1) * (fac n:num)`;
val def = Define `the_value = 1:num`;
val def = Define `goo k = next k + 1`;
val def = Define `next n = n+1:num`;
val ty = ``:'a + 'b``; register_type ty;
val ty = ``:'a option``; register_type ty;
val def = Define `goo k = next k + 1`;

*)

fun translate def = (let
  val original_def = def
  fun the (SOME x) = x | the _ = failwith("the of NONE")
  (* preprocessing: reformulate def, read off info and register types *)
  val _ = register_term_types (concl def)
  val (is_rec,defs,ind) = preprocess_def def
  val _ = register_term_types (concl (LIST_CONJ defs))
  val info = map get_info defs
  val msg = comma (map (fn (fname,_,_,_) => fname) info)
  (* derive deep embedding *)
  fun compute_deep_embedding info = let
    val _ = map (fn (fname,lhs,_,_) => install_rec_pattern lhs fname) info
    val thms = map (fn (fname,lhs,rhs,def) => (fname,hol2deep rhs,def)) info
    val _ = uninstall_rec_patterns ()
    in thms end
  fun loop info =
    compute_deep_embedding info
    handle UnableToTranslate tm => let
      val _ = is_const tm orelse raise (UnableToTranslate tm)
      val _ = translate ((!find_def_for_const) tm)
      in loop info end
(*
val _ = map (fn (fname,lhs,_,_) => install_rec_pattern lhs fname) info
val (fname,lhs,rhs,def) = el 1 info
can (find_term is_arb) (rhs |> rand |> rator)
*)
  val thms = loop info
  val _ = print ("Translating " ^ msg ^ "\n")
  (* postprocess raw certificates *)
(*
val (fname,th,def) = hd thms
*)
  fun optimise_and_abstract (fname,th,def) = let
    (* replace rhs with lhs *)
    val th = th |> CONV_RULE ((RAND_CONV o RAND_CONV)
             (REWRITE_CONV [CONTAINER_def] THENC ONCE_REWRITE_CONV [GSYM def]))
    (* optimise generated code *)
    val th = MATCH_MP Eval_OPTIMISE (UNDISCH_ALL th)
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th |> D
    (* prove lookup_cons *)
    val th = clean_lookup_cons th
    (* abstract parameters *)
    val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
    val (th,v) = if (length rev_params = 0) then (th,T) else
                   (foldr (fn (v,th) => apply_Eval_Fun v th true) th
                      (rev (if is_rec then butlast rev_params else rev_params)),
                    last rev_params)
    in (fname,def,th,v) end
  val thms = map optimise_and_abstract thms

  (* final phase: extract precondition, perform induction, store cert *)
(*
val _ = (max_print_depth := 25)
*)

  val th = if not is_rec then let
    (* non-recursive case *)
    val _ = length thms = 1 orelse failwith "multiple non-rec definitions"
    val (code_def,(fname,def,th,v)) = abbrev_code (hd thms)
    (* remove parameters *)
    val th = D (clean_assumptions th)
    val th = CONV_RULE (QCONV (DEPTH_CONV ETA_CONV)) th
    val th = Q.INST [`shaddow_env`|->`env`] th |> REWRITE_RULE []
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
                        (SIMP_CONV std_ss [EVAL ``CONTAINER TRUE``,
                                           EVAL ``CONTAINER FALSE``])) th
    val th = clean_assumptions th
    val (lhs,rhs) = dest_eq (concl def)
    val pre_var = get_pre_var lhs fname
    val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
    val (th,pre) = extract_precondition_non_rec th pre_var
    val th = remove_Eq th
    (* simpliy EqualityType *)
    val th = SIMP_EqualityType_ASSUMS th
    (* DeclAssumExists *)
    val decl_assum_x = let
      val thi = PURE_REWRITE_RULE [code_def] th
      in if length rev_params = 0 then
           MATCH_MP (INST_mn DeclAssumExists_SNOC_Dlet)
             ((DISCH (get_DeclAssum()) thi) |> Q.GENL [`tys`,`env`])
         else (INST_mn DeclAssumExists_SNOC_Dlet_Fun) end
    (* abbreviate code *)
    val fname_str = stringLib.fromMLstring fname
    val th = th |> DISCH_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
    val th = th |> DISCH (get_DeclAssum ()) |> Q.GEN `env`
                |> MATCH_MP (INST_mn DeclAssum_Dlet_INTRO)
                |> SPEC fname_str |> Q.SPEC `env`
                |> PURE_ONCE_REWRITE_RULE [code_def] |> UNDISCH_ALL
    val _ = code_def |> (delete_const o fst o dest_const o fst o dest_eq o concl)
    (* store certificate for later use *)
    val pre = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
    val th = print_time "store_cert non-rec" (store_cert th [pre]) decl_assum_x |> Q.SPEC `env` |> UNDISCH_ALL
    val _ = print_fname fname def (* should really be original def *)
    in th end
    else (* is_rec *) let

    (* abbreviate code *)
    val (code_defs,thms) = let val x = map abbrev_code thms
                           in (map fst x, map snd x) end
    (* introduce Recclosure *)
    fun mk_Recclosure_part (fname,def,th,v) = let
      val fname = fname |> stringLib.fromMLstring
      val name = v |> dest_var |> fst |> stringLib.fromMLstring
      val body = th |> UNDISCH_ALL |> concl |> rator |> rand
      in ``(^fname,^name,^body)`` end
    val parts = map mk_Recclosure_part thms
    val recc = listSyntax.mk_list(parts,type_of (hd parts))
    fun apply_recc (fname,def,th,v) = let
      val th = apply_Eval_Recclosure recc fname v th
      val th = clean_assumptions th
      val th = CONV_RULE (QCONV (DEPTH_CONV ETA_CONV)) th
      val th = Q.INST [`env2`|->`cl_env`,`shaddow_env`|->`cl_env`] th |> RW []
               |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss [EVAL_T_F]))
      val th = clean_assumptions th
      in (fname,def,th) end
    val thms = map apply_recc thms
    (* DeclAssumExists lemma *)
    val c = REWRITE_CONV [MAP,FST] THENC EVAL
    val c = RATOR_CONV (RAND_CONV c)
    val decl_assum_x = SPEC recc (INST_mn DeclAssumExists_SNOC_Dletrec)
                         |> SPEC_ALL |> CONV_RULE c |> (fn th => MATCH_MP th TRUTH)
    (* collect precondition *)
    val thms = extract_precondition_rec thms
    (* apply induction *)
    fun get_goal (fname,def,th,pre) = let
      val th = REWRITE_RULE [CONTAINER_def] th
      val hs = hyp th
      val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
      val hyp_tm = list_mk_abs(rev rev_params, th |> UNDISCH_ALL |> concl)
      val goal = list_mk_forall(rev rev_params, th |> UNDISCH_ALL |> concl)
      in (hyp_tm,(th,(hs,goal))) end
    val goals = map get_goal thms
    val gs = goals |> map (snd o snd o snd) |> list_mk_conj
    val hs = goals |> map (fst o snd o snd) |> flatten
                   |> all_distinct |> list_mk_conj
    val goal = mk_imp(hs,gs)
    val ind_thm = (the ind)
                  |> rename_bound_vars_rule "i" |> SIMP_RULE std_ss []
                  |> SPECL (goals |> map fst)
                  |> CONV_RULE (DEPTH_CONV BETA_CONV)
    fun POP_MP_TACs ([],gg) = ALL_TAC ([],gg)
      | POP_MP_TACs (ws,gg) =
          POP_ASSUM (fn th => (POP_MP_TACs THEN MP_TAC th)) (ws,gg)
    val pres = map (fn (_,_,_,pre) => case pre of SOME x => x | _ => TRUTH) thms

    (*
      set_goal([],goal)
    *)
    val lemma =
      auto_prove "ind" (goal,
        STRIP_TAC
        \\ MATCH_MP_TAC ind_thm
        \\ REPEAT STRIP_TAC
        \\ FIRST (map MATCH_MP_TAC (map (fst o snd) goals))
        \\ REPEAT STRIP_TAC
        \\ POP_MP_TACs
        \\ SIMP_TAC (srw_ss()) [ADD1,TRUE_def,FALSE_def]
        \\ SIMP_TAC std_ss [UNCURRY_SIMP]
        \\ SIMP_TAC std_ss [GSYM FORALL_PROD]
        \\ METIS_TAC [])
      handle HOL_ERR _ =>
      auto_prove "ind" (goal,
        STRIP_TAC
        \\ SIMP_TAC std_ss [FORALL_PROD]
        \\ (MATCH_MP_TAC ind_thm ORELSE
            MATCH_MP_TAC (SIMP_RULE bool_ss [FORALL_PROD] ind_thm))
        \\ REPEAT STRIP_TAC
        \\ FIRST (map MATCH_MP_TAC (map (fst o snd) goals))
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ REPEAT STRIP_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ FULL_SIMP_TAC std_ss [UNCURRY_SIMP]
        \\ METIS_TAC [])
      handle HOL_ERR _ =>
      auto_prove "ind" (goal,
        STRIP_TAC
        \\ SIMP_TAC std_ss [FORALL_PROD]
        \\ (MATCH_MP_TAC ind_thm ORELSE
            MATCH_MP_TAC (SIMP_RULE bool_ss [FORALL_PROD] ind_thm))
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC PreImp_IMP
        \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV pres))
        \\ (STRIP_TAC THENL (map MATCH_MP_TAC (map (fst o snd) goals)))
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ REPEAT STRIP_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ FULL_SIMP_TAC std_ss [UNCURRY_SIMP,PRECONDITION_def]
        \\ METIS_TAC [])
      handle HOL_ERR _ =>
      auto_prove "ind" (mk_imp(hs,ind_thm |> concl |> rand),
        STRIP_TAC
        \\ MATCH_MP_TAC ind_thm
        \\ REPEAT STRIP_TAC
        \\ FIRST (map MATCH_MP_TAC (map (fst o snd) goals))
        \\ REPEAT STRIP_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ METIS_TAC [])
    val results = UNDISCH lemma |> CONJUNCTS |> map SPEC_ALL

(*
val (th,(fname,def,_,pre)) = hd (zip results thms)
*)
    (* clean up *)
    fun fix (th,(fname,def,_,pre)) = let
      val th = let
        val thi = MATCH_MP IMP_PreImp_THM th
        val thi = CONV_RULE ((RATOR_CONV o RAND_CONV)
                    (ONCE_REWRITE_CONV [force_thm_the pre] THENC
                     SIMP_CONV std_ss [PRECONDITION_def])) thi
        val thi = MP thi TRUTH
        in thi end handle HOL_ERR _ => th
      val th = RW [PreImp_def] th |> UNDISCH_ALL
      val th = remove_Eq th
      val th = SIMP_EqualityType_ASSUMS th
      val th = th |> DISCH_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
      in (fname,def,th,pre) end
    val results = map fix (zip results thms)
    val recc = results |> map (fn (fname,def,th,pre) => th) |> hd |> hyp
      |> first (can (find_term (fn tm => tm = rator ``Recclosure e``)))
    val recs = recc |> rand |> rator |> rand |> listSyntax.dest_list |> fst
    val Ps = results |> map (fn (_,_,th,_) => th |> concl |> rand)
    val Precs = zip Ps recs |> map (pairSyntax.mk_pair)
                |> map (fn tm => pairSyntax.mk_pair(genvar(``:bool``),tm))
    val Precs_tm = listSyntax.mk_list(Precs,type_of (hd Precs))
    (* introduce letrec declaration *)
    val lemma =
      SPEC Precs_tm (INST_mn DeclAssum_Dletrec_INTRO_ALT)
      |> REWRITE_RULE [EVERY_DEF]
      |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
      |> REWRITE_RULE [GSYM CONJ_ASSOC,MAP,o_THM]
    val ss = subst [``env1:all_env``|->``env:all_env``,
                    ``env:all_env``|->``cl_env:all_env``]
    val ts = lemma |> concl |> dest_imp |> fst
                   |> dest_forall |> snd |> dest_forall |> snd
                   |> ss |> dest_imp |> fst
                   |> list_dest dest_conj |> tl
    val th = results |> map (fn (_,_,th,_) => let
               val hs = hyp th |> filter (can (match_term ``PRECONDITION p``))
               val th = foldr (uncurry DISCH) th hs
               val th = REWRITE_RULE [AND_IMP_INTRO] th
               val imp = th |> concl |> is_imp
               val th = if imp then th else DISCH T th
               val th = CONV_RULE (REWR_CONV (GSYM CONTAINER_def)) th
               in th end) |> LIST_CONJ
    val th = foldr (fn (x,th) => DISCH x th) th ts
                   |> DISCH (ss (get_DeclAssum ()))
                   |> PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
                   |> Q.GEN `cl_env` |> Q.GEN `env`
                   |> PURE_REWRITE_RULE [CONTAINER_def]
    val th = MATCH_MP lemma th |> Q.SPEC `env` |> DISCH_ALL
             |> PURE_ONCE_REWRITE_RULE code_defs |> UNDISCH_ALL
    val decl_assum_x = PURE_ONCE_REWRITE_RULE code_defs decl_assum_x
    val _ = code_defs |> map
              (delete_const o fst o dest_const o fst o dest_eq o concl)
    (* store certificate for later use *)
    val pres = map (fn (fname,def,th,pre) => force_thm_the pre) thms
    val th = print_time "store_cert" (store_cert th pres) decl_assum_x
                |> CONJUNCTS |> map (UNDISCH_ALL o Q.SPEC `env`) |> LIST_CONJ
    val (fname,def,_,_) = hd thms
    val _ = print_fname fname def (* should be original def *)
    in th end
  fun check th = let
    val f = can (find_term (can (match_term
              ``WF:('a -> 'a -> bool) -> bool``))) (th |> D |> concl)
    in if f then failwith "WR" else th end
  in check th end handle UnableToTranslate tm => let
    val _ = print "\n\nCannot translate term:  "
    val _ = print_term tm
    val _ = print "\n\nwhich has type:\n\n"
    val _ = print_type (type_of tm)
    val _ = print "\n\n"
    in raise UnableToTranslate tm end)
  handle e => let
   val names =
     def |> SPEC_ALL |> CONJUNCTS
         |> map (fst o dest_const o repeat rator o fst o dest_eq o concl o SPEC_ALL)
         |> all_distinct handle HOL_ERR _ => ["<unknown name>"]
   val _ = print ("Failed translation: " ^ comma names ^ "\n")
   in raise e end;

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

end
