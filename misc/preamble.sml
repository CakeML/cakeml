(*
   Proof tools (e.g. tactics) used throughout the development.
*)
structure preamble =
struct
local open intLib wordsLib in end;
open set_relationTheory; (* comes first so relationTheory takes precedence *)
open ASCIInumbersTheory BasicProvers Defn HolKernel Parse SatisfySimps Tactic
     monadsyntax alistTheory alignmentTheory arithmeticTheory bagTheory boolLib
     boolSimps bossLib byteTheory containerTheory combinTheory dep_rewrite
     finite_mapTheory indexedListsTheory listTheory llistTheory
     lprefix_lubTheory markerLib miscTheory mp_then optionTheory pairLib
     pairTheory pred_setTheory quantHeuristicsLib relationTheory res_quanTheory
     rich_listTheory sortingTheory sptreeTheory stringTheory sumTheory
     wordsTheory;
(*Temporary workaround for cache being slow on long files*)
fun clear_cache_prover gtac  =
 let
   val _ = List.app Cache.clear_cache [numSimps.arith_cache, intSimps.omega_cache,
                                       intSimps.cooper_cache]
   val res = TAC_PROOF gtac
   val _ = List.app Cache.clear_cache [numSimps.arith_cache, intSimps.omega_cache,
                                       intSimps.cooper_cache]
 in
   res
 end
val _ = Tactical.set_prover clear_cache_prover;

(* TOOD: move? *)
val wf_rel_tac = WF_REL_TAC
val induct_on = Induct_on
val cases_on = Cases_on;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;
val sym_sub_tac = SUBST_ALL_TAC o SYM;
fun asm_match q = Q.MATCH_ASSUM_RENAME_TAC q
val match_exists_tac = part_match_exists_tac (hd o strip_conj)
val asm_exists_tac = first_assum(match_exists_tac o concl)
val has_pair_type = can dest_prod o type_of
fun impl_subgoal_tac th =
  let
    val hyp_to_prove = lhand (concl th)
  in
    SUBGOAL_THEN hyp_to_prove (fn thm => assume_tac (MP th thm))
  end;

(* -- *)

fun check_tag t = Tag.isEmpty t orelse Tag.isDisk t
fun check_thm t = (
  prove(T, fn g => (
    (if check_tag (Thm.tag t) then () else failwith "theorem depends on cheats");
    ACCEPT_TAC TRUTH g));
  t)

val option_bind_tm = prim_mk_const{Thy="option",Name="OPTION_BIND"};
val option_ignore_bind_tm = prim_mk_const{Thy="option",Name="OPTION_IGNORE_BIND"};
val option_guard_tm = prim_mk_const{Thy="option",Name="OPTION_GUARD"};

structure option_monadsyntax = struct
fun temp_add_option_monadsyntax() =
  let
    open monadsyntax
  in
    temp_enable_monadsyntax ();
    temp_enable_monad "option"
  end

fun add_option_monadsyntax() =
  let
    open monadsyntax
  in
    enable_monadsyntax();
    enable_monad "option"
  end
end

val _ = set_trace"Goalstack.print_goal_at_top"0 handle HOL_ERR _ => set_trace"goalstack print goal at top"0

(* treat the given eq_tms (list of equations) as rewrite thereoms,
   return the resulting term, note we can't return a theorem because
   the equations might not be theorems -- indeed, in many cases they
   won't be theorems.
*)
fun term_rewrite eq_tms tm =
  tm |> QCONV (PURE_REWRITE_CONV (map (curry mk_thm []) eq_tms))
     |> concl |> rhs

(* TODO: move to Lib (or Portable)? *)
fun itlist3 f L1 L2 L3 base_value =
  let
    fun itl ([], [], []) = base_value
      | itl (a :: rst1, b :: rst2, c :: rst3) = f a b c (itl (rst1, rst2, rst3))
      | itl _ = raise mk_HOL_ERR "Lib" "itlist3" "lists of different length"
    in
      itl (L1, L2, L3)
    end

fun zip3 ([],[],[]) = []
  | zip3 ((h1::t1),(h2::t2),(h3::t3)) = ((h1,h2,h3)::zip3(t1,t2,t3))
  | zip3 _ = raise mk_HOL_ERR "Lib" "zip3" "lists of different length"

infix 8 $
fun op $ (f,x) = f x

fun pad_to sz str =
  CharVector.tabulate(Int.max(0,sz-String.size str),K #" ")^str

val sum = foldl (op+) 0

fun println s = print (strcat s "\n");
(* -- *)

(* TODO: move to listLib (and move MAP3 to listTheory) *)
val (map3_tm,mk_map3,dest_map3,is_map3) = syntax_fns4 "misc" "MAP3"

local
  val (m3n,m3c) = CONJ_PAIR MAP3_def
  val m3c = CONV_RULE(RESORT_FORALL_CONV(sort_vars["f","h1","h2","h3","t1","t2","t3"])) m3c
in
  fun MAP3_CONV conv tm =
    let
      val (fnn,l1,l2,l3) = dest_map3 tm
      val (els1,_) = listSyntax.dest_list l1
      val (els2,_) = listSyntax.dest_list l2
      val (els3,_) = listSyntax.dest_list l3
      val nth = ISPEC fnn m3n
      val cth = ISPEC fnn m3c
      val cns = rator(rator(rand(snd(strip_forall(concl cth)))))
      fun APcons t1 t2 = MK_COMB(AP_TERM cns t2,t1)
      fun itfn e1 e2 e3 th =
        let
          val ts = tl(#2(strip_comb(rand(rator(concl th)))))
          val es = [e1,e2,e3]
          val th1 = SPECL ts (SPECL es cth)
        in
          TRANS th1 (APcons th (conv (list_mk_comb(fnn,es))))
        end
    in
      itlist3 itfn els1 els2 els3 nth
    end
end
(* -- *)

(* parlist num_threads chunk_size eval_fn ls :
   evaluate (eval_fn i n x) on each element x of list ls
     - using num_threads threads
     - each working on chunks of ls of size up to chunk_size
     - where i = chunk index, and n = index within chunk, for x
     - returns the list of results in reverse order
   Uses Poly/ML's Thread structure, so not portable.
   Replace with a portable parallel map (does it exist)?
*)
local
  open Thread
  fun chunks_of n ls =
    let
      val (ch,rst) = split_after n ls
    in
      if null rst then [ch]
      else ch::(chunks_of n rst)
    end handle HOL_ERR _ => [ls]
in
  fun parlist num_threads chunk_size eval_fn ls =
    let
      val num_items = List.length ls
      val chs = chunks_of chunk_size ls
      val num_chunks = List.length chs

      fun eval_chunk i n [] acc = acc
        | eval_chunk i n (x::xs) acc =
          eval_chunk i (n+1) xs (eval_fn i n x::acc)

      val mutex = Mutex.mutex()
      val refs = List.tabulate(num_chunks,(fn _ => ref NONE))
      val threads_left = ref num_threads
      val threads_left_mutex = Mutex.mutex()
      val cvar = ConditionVar.conditionVar()

      fun find_work i [] [] =
            let
              val () = Mutex.lock threads_left_mutex
              val () = threads_left := !threads_left-1
              val () = Mutex.unlock threads_left_mutex
            in ConditionVar.signal cvar end
        | find_work i (r::rs) (c::cs) =
           (case (Mutex.lock mutex; !r) of
              SOME _ => (Mutex.unlock mutex; find_work (i+1) rs cs)
            | NONE =>
              let
                val () = r := SOME []
                val () = Mutex.unlock mutex
                val vs = eval_chunk i 0 c []
                val () = r := SOME vs
              in
                find_work (i+1) rs cs
              end)
       | find_work _ _ _ =
           raise mk_HOL_ERR "Lib" "parlist" "lists of different length"

      fun fork_this () = find_work 0 refs chs

      val _ = Mutex.trylock threads_left_mutex orelse raise General.Bind

      val () = for_se 1 num_threads
        (fn _ => ignore (Thread.fork (fork_this, [Thread.EnableBroadcastInterrupt true])))

      fun wait () =
        if !threads_left = 0 then Mutex.unlock threads_left_mutex
        else (ConditionVar.wait(cvar,threads_left_mutex); wait())

      val () = wait()
    in
      List.concat (List.map (Option.valOf o op!) (List.rev refs))
    end
end

(* map_ths_conv
    [|- f xn = vn, ..., |- f x1 = v1]
    ``MAP f [x1; ...; xn]``
   produces
     |- MAP f [x1; ...; xn] = [v1; ...; vn]
*)
fun map_ths_conv ths =
  let
    val next_thm = ref ths
    fun el_conv _ =
      case !next_thm of
         th :: rest => let val () = next_thm := rest in th end
       | _ => raise mk_HOL_ERR "preamble" "map_ths_conv" ""
  in
    listLib.MAP_CONV el_conv
  end

val rconc = rhs o concl;

local
  val pad = pad_to 30
in
fun time_with_size size_fn name eval_fn x =
  let
    val () = Lib.say(pad (name^" eval: "))
    val (timer,real_timer) = (start_time(), start_real_time())
    val r = eval_fn x
    val () = end_time timer
    val () = Lib.say(String.concat[pad (name^" real: "),
               Lib.time_to_string(Timer.checkRealTimer real_timer),"\n"])
    val z = size_fn r
    val () = Lib.say(String.concat[pad (name^" size: "),Int.toString z,"\n"])
  in r end
end

fun thms_size ls = sum (map (term_size o rconc) ls)

fun timez x y = time_with_size (term_size o rconc) x y

fun mk_abbrev_name s = String.concat[s,!Defn.def_suffix]
fun mk_abbrev s tm =
  new_definition(mk_abbrev_name s,
                 mk_eq(mk_var(s,type_of tm),tm))

fun make_abbrevs str n [] acc = acc
  | make_abbrevs str n (t::ts) acc =
    make_abbrevs str (n-1) ts
      (mk_abbrev (str^(Int.toString n)) t :: acc)

fun intro_abbrev [] tm = raise UNCHANGED
  | intro_abbrev (ab::abbs) tm =
      FORK_CONV(REWR_CONV(SYM ab),intro_abbrev abbs) tm

fun Abbrev_intro th =
  EQ_MP (SYM(SPEC(concl th)markerTheory.Abbrev_def)) th

val preamble_ERR = mk_HOL_ERR"preamble"

fun subterm f = partial(preamble_ERR"subterm""not found") (bvk_find_term (K true) f)

fun any_match_mp impth th =
  let
    val h = impth |> concl |> strip_forall |>snd |> dest_imp |> fst |>strip_conj
    val c = first(can (C match_term (concl th))) h
    val th2 = impth
      |> CONV_RULE (STRIP_QUANT_CONV(LAND_CONV(move_conj_left (aconv c))))
      |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
  in
    MATCH_MP th2 th  end

val SWAP_IMP = let
  val P = mk_var("P", bool)
  val Q = mk_var("Q", bool)
  val R = mk_var("R", bool)
in
  Feedback.trace ("meson", 0) (PROVE[])
    (mk_imp(list_mk_imp([P,Q], R), list_mk_imp([Q,P], R)))
end

fun prove_hyps_by tac th = foldr (uncurry PROVE_HYP) th (map (fn h => prove(h,tac)) (hyp th));

(* if the first conjunct under the goal's existential prefix matches the term
   except for some places where it has structure and the term just has variables,
   then pair split all those variables *)
fun split_pair_match tm (g as (_,w)) =
  let
    val (vs,b) = strip_exists w
    val cs = strip_conj b val c = hd cs
    val cs = op::(strip_comb c)
    val ts = op::(strip_comb tm)
    val ss = map2 (total o match_term) ts cs
    val vs = map ((fn x => map #redex (Option.valOf x) handle _ => []) o
                  (Option.map fst)) ss
    val vs = flatten vs
    val _ = assert(List.all (fn (x,y) => not (is_const x) orelse isSome y)) (zip cs ss)
  in
    map_every (TRY o PairCases_on) (map (C cons [] o ANTIQUOTE) vs)
  end g

(* the theorem is of the form [!x1 .. xn. P] and the goal contains a subterm
   [f v1 .. vn]. apply ttac to [P[vi/xi]]. *)
fun specl_args_of_then f th (ttac:thm_tactic) (g as (_,w)) =
  let
    val t = find_term (same_const f o fst o strip_comb) w
    val (_,vs) = strip_comb t
  in
    ttac (ISPECL vs th)
  end g

(* TODO: all the following might not be used? *)

(* the theorem is of the form [!x1 ... xn. P ==> ?y1 ... ym. Q /\ ...]
   the goal is of the form [?z1 ... zk. Q' /\ ...]
   instantiate the xs as necessary to make Q and Q' match as much as possible
   (complete match impossible if some of Q's variables are the ys) *)
fun exists_match_mp_then (ttac:thm_tactic) th (g as (_,w)) =
  let
    val (ws,b) = strip_exists w
    val cs = strip_conj b val c = hd cs
    val (vs,t) = strip_forall (concl th)
    val vs = map (fst o dest_var o variant (free_vars b)) vs
    val th = CONV_RULE (RENAME_VARS_CONV vs) th
    val (vs,t) = strip_forall (concl th)
    val (_,b) = dest_imp t
    val (_,b) = strip_exists b
    val ts = strip_conj b val t = hd ts
    val (tms,_) = match_term t c
    val tms = filter (C (op_mem aconv) vs o #redex) tms
    val tms = filter (not o C (op_mem aconv) ws o #residue) tms
    val xs = map #redex tms
    val ys = map #residue tms
    fun sorter ls = xs@(filter (not o C (op_mem aconv) xs) ls)
    val th = SPECL ys (CONV_RULE (RESORT_FORALL_CONV sorter) th)
  in
    ttac th
  end g

(* the theorem is of the form [!x1..n. P ==> Q]
   the goal is of the form [?y1..n. Q' /\ ...]
   replace the goal with [?y1..n. P /\ ...] by
   making the Q and Q' match *)
fun exists_suff_tac th (g as (_,w)) =
  let
    val (ws,b) = strip_exists w
    val bs = strip_conj b
    val th = GEN_ALL(PART_MATCH (snd o dest_imp) th (hd bs))
    val (vs,c) = strip_forall (concl th)
    val (b',_) = dest_imp c
  in
    suff_tac(list_mk_exists(ws,list_mk_conj(b'::tl bs))) >- metis_tac[th]
  end g

(* the theorem is of the form [!x1..n. P ==> ?y1..m. Q /\ A]
   the goal is of the form [?z1..k. Q' /\ B]
   specialise the theorem to make Q and Q' match as much as possible then
   regeneralise then apply the theorem tactic *)
fun exists_suff_gen_then ttac th (g as (_,w)) =
  let
    val (ws,b) = strip_exists w
    val bs = strip_conj b
    val th = (GEN_ALL(PART_MATCH (hd o strip_conj o snd o strip_exists o snd o dest_imp) th (hd bs)))
  in ttac th end g

(* the theorem is of the form [!x1..n. P ==> ?y1..m. Q /\ A]
   the goal is of the form [?z1..k. Q' /\ B]
   specialise the theorem to make Q and Q' match as much as possible then
   apply the theorem tactic *)
fun exists_suff_then ttac th (g as (_,w)) =
  let
    val (ws,b) = strip_exists w
    val bs = strip_conj b
    val th = (PART_MATCH (hd o strip_conj o snd o strip_exists o snd o dest_imp) th (hd bs))
  in ttac th end g

fun loseC c =
    first_x_assum
      (K ALL_TAC o assert (can (find_term (same_const c)) o concl))

val kill_asm_guard =
    disch_then (fn th => SUBGOAL_THEN (lhand (concl th))
                                      (MP_TAC o MATCH_MP th)) >- simp[]

fun qispl_then [] ttac = ttac
  | qispl_then (q::qs) ttac = Q.ISPEC_THEN q (qispl_then qs ttac)
fun qxchl [] ttac = ttac
  | qxchl (q::qs) ttac = Q.X_CHOOSE_THEN q (qxchl qs ttac)
val rveq = rpt BasicProvers.VAR_EQ_TAC

fun erule k th = let
  fun c th = let
    val (vs, body) = strip_forall (concl th)
  in
    if is_imp body then
      first_assum (c o MATCH_MP th) ORELSE
      first_assum (c o MATCH_MP th o SYM)
    else k th
  end
  fun is_resolvable th = let
    val (vs, body) = strip_forall (concl th)
  in
    is_imp body
  end
in
  if is_resolvable th then c th else NO_TAC
end

fun print_tac s (g as (asl,w)) = let
  fun mmlnt_test t = is_const t andalso type_of t = ``:MMLnonT``
in
  case get_first (Lib.total (find_term mmlnt_test)) asl of
      NONE => raise Fail "No MMLnonT in goal"
    | SOME t => if term_to_string t = s then
                  (print ("print_tac: "^s^"\n"); ALL_TAC g)
                else raise Fail ("MMLnonT not "^s)
end

fun simple_match_mp th1 th2 = let
  val (x,y) = dest_imp (concl th1)
  val (i,t) = match_term x (concl th2)
  in MP (INST i (INST_TYPE t th1)) th2 end

(* ========================================================================= *)
(* Execute processes on Posix systems and read results from stdout.          *)
(*                                                                           *)
(* The implementation is modeled after that of the Unix struct in the PolyML *)
(* implementation of the SML basis library.                                  *)
(* ========================================================================= *)

fun read_process (cmd, args, dir) =
  let
    open Unix
    open OS

    fun search_paths t []      = NONE
      | search_paths t (p::ps) =
          let
            val cmd = Path.concat (p, t)
          in
            if FileSys.access (cmd, [FileSys.A_READ, FileSys.A_EXEC]) then
              SOME cmd
            else
              search_paths t ps
          end

    fun get_cmd t =
      case Process.getEnv "PATH" of
        NONE      => search_paths t ["."]
      | SOME path =>
          let
            val paths = String.tokens (fn c => c = #":") path
          in
            search_paths t paths
          end

    val old_pwd = FileSys.getDir ()
    val _ =
      case dir of
        NONE => ()
      | SOME d => FileSys.chDir d
  in
    case get_cmd cmd of
      NONE => NONE
    | SOME cmd =>
        let
          val proc = execute (cmd, args)
          val outp = TextIO.inputAll (textInstreamOf proc)
          val str = String.substring (outp, 0, String.size outp - 1)
        in
          if Option.isSome dir then FileSys.chDir old_pwd else ();
          if Process.isSuccess (reap proc) then SOME str else NONE
        end
  end
  handle _ => NONE

(* Run an external process and get its stdout as a string option term *)
fun tm_from_proc cmd args =
  case read_process (cmd, args, NONE) of
    NONE => Term `NONE : string option`
  | SOME s => Term `SOME ^(stringSyntax.fromMLstring s)`

fun tm_from_proc_from dir cmd args =
  case read_process (cmd, args, SOME dir) of
    NONE => Term `NONE : string option`
  | SOME s => Term `SOME ^(stringSyntax.fromMLstring s)`

(* Run an external process and get its stdout as a mlstring option term *)
fun mlstring_from_proc cmd args =
  case read_process (cmd, args, NONE) of
    NONE => Term `NONE : mlstring option`
  | SOME s => Term `SOME (strlit ^(stringSyntax.fromMLstring s))`

(* ========================================================================= *)
(* ========================================================================= *)

local
  open stringLib Boolconv ListConv1 pred_setLib;
  val [ALL_DISTINCT_NIL,ALL_DISTINCT_CONS] = ALL_DISTINCT |> CONJUNCTS
  val [MEM_NIL,MEM_CONS] = MEM |> CONJUNCTS
  val [FLAT_NIL,FLAT_CONS] = FLAT |> CONJUNCTS
  val [MAP_NIL,MAP_CONS] = MAP |> CONJUNCTS
  val [APPEND_NIL_LEFT,APPEND_CONS] = APPEND |> CONJUNCTS
  val APPEND_NIL_RIGHT = APPEND_NIL |> CONJUNCTS |> hd
  val [set_nil,set_cons] = LIST_TO_SET |> CONJUNCTS
in

  (* TODO: move to listLib, consolidate with IS_EL_CONV *)
  fun mem_conv eq_conv tm =
    tm |> (
      REWR_CONV MEM_NIL
      ORELSEC
     (REWR_CONV MEM_CONS
       THENC RATOR_CONV(RAND_CONV(eq_conv))
       THENC OR_CONV
       THENC (fn tm => if Teq tm then ALL_CONV tm else mem_conv eq_conv tm))
     )

  (* TODO: move to listLib, cf. Z3ProofReplay.ALL_DISTINCT_CONV *)
  fun all_distinct_conv eq_conv tm =
    tm |> (
       REWR_CONV ALL_DISTINCT_NIL
       ORELSEC
       (REWR_CONV ALL_DISTINCT_CONS
        THENC RATOR_CONV(RAND_CONV(RAND_CONV(mem_conv eq_conv)))
        THENC RATOR_CONV(RAND_CONV(NOT_CONV))
        THENC AND_CONV
        THENC (fn tm => if Feq tm then ALL_CONV tm else all_distinct_conv eq_conv tm)
       )
    )

  val all_distinct_string_conv = all_distinct_conv string_EQ_CONV
  val all_distinct_list_string_conv = all_distinct_conv (list_EQ_CONV string_EQ_CONV)

  fun set_conv tm =
    tm |>
    (
      REWR_CONV set_nil
      ORELSEC
      (REWR_CONV set_cons THENC RAND_CONV set_conv)
    )
end
local
fun BRING_NAME_TO_FRONT_CONV n t =
    let val (vs, b) = strip_forall t
    in
      case vs of
          [] => NO_CONV
        | v::rest => if #1 (dest_var v) = n then ALL_CONV
                     else BINDER_CONV (BRING_NAME_TO_FRONT_CONV n) THENC
                          SWAP_VARS_CONV
    end t

fun SPECtop th =
    let val (v, _) = dest_forall (concl th)
    in
      SPEC v th
    end

fun SPECnames [] th = th
  | SPECnames (n::ns) th =
    case Lib.total (CONV_RULE (BRING_NAME_TO_FRONT_CONV n)) th of
        NONE => SPECnames ns th
      | SOME th' => SPECnames ns (SPECtop th')

fun specnames_then fvnms ttac th = ttac (SPECnames fvnms th)
in
fun old_drule_then ttac th =
    let val fvnames = map (#1 o dest_var) (th |> concl |> free_vars)
    in
      drule_then (specnames_then fvnames ttac) th
    end
val old_drule = old_drule_then mp_tac
fun old_dxrule_then ttac th =
    let val fvnames = map (#1 o dest_var) (th |> concl |> free_vars)
    in
      dxrule_then (specnames_then fvnames ttac) th
    end
val old_dxrule = old_dxrule_then mp_tac

end


end
