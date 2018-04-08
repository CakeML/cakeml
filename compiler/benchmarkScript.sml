open preamble
     parsingComputeLib compilationLib
     basisProgTheory

(* TODO: Not too sure why parsingComputeLib has to be opened to get EVAL to
   work for parsing *)

val _ = new_theory "benchmark"

(* Check that a prog represented as a string parses and type checks
   Returns the parsed program it if typechecks
*)

fun check_prog str =
let
  val parsed = rconc (EVAL ``parse_prog (lexer_fun ^(stringSyntax.fromMLstring str))``)
in
  if optionSyntax.is_some parsed then
    let
      val parsed = optionSyntax.dest_some parsed
    in
      SOME(rconc (EVAL``basis ++ ^(parsed)``))
    end
  else
    NONE
end;

val btree_str =
  "datatype tree = Leaf"^
  "              | Branch of tree * int * tree;"^
  "fun insert x t ="^
  "  case t "^
  "  of Leaf => (Branch(Leaf,x,Leaf))"^
  "  |  Branch(t1,y,t2) => (if (x < y)"^
  "                         then (Branch(insert x t1,y,t2)) "^
  "                         else (if (y < x)"^
  "                               then (Branch(t1,y,insert x t2))"^
  "                               else (Branch(t1,y,t2))));"^
  "fun build_tree l ="^
  "  case l"^
  "  of [] => Leaf"^
  "  |  x::xs => (insert x (build_tree xs));"^
  "fun append l ys ="^
  "  case l"^
  "  of [] => ys"^
  "  |  x::xs => (x::(append xs ys));"^
  "fun flatten t ="^
  "  case t"^
  "  of Leaf => []"^
  "  |  Branch(t1,x,t2) => (append (flatten t1) (append [x] (flatten t2)));"^
  "fun tree_sort xs = flatten (build_tree xs);"^
  "fun mk_list n ="^
  "  if (n = 0)"^
  "  then []"^
  "  else (n::(mk_list (n - 1)));"^
  "fun use_tree n = tree_sort (append (mk_list n) (mk_list n));"^
  "val test = use_tree 10000;";

val btree = check_prog btree_str

val fib_str =
  "fun fib n = if (n < 2) then n else ((fib (n - 1)) + (fib (n - 2)));"^
  "fun use_fib n = (((((fib n) + (fib n)) + (fib n)) + (fib n)) + (fib n)) + (fib n);"^
  "val test = use_fib 36;"

val fib = check_prog fib_str;

val foldl_str =
  "fun foldl f e xs ="^
  "  case xs of [] => e"^
  "  | (x::xs) => foldl f (f e x) xs;"^
  "fun repeat x n ="^
  "  if (n = 0)"^
  "  then []"^
  "  else (x::(repeat x (n - 1)));"^
  "val test = foldl (fn x => fn y => x + (foldl (fn x => fn y => x+y) 0 y)) 0"^
  "           (repeat (repeat 1 15000) 15000);"

val foldl = check_prog foldl_str;

(* TODO: Note!! benchmark updated!! *)
val nqueens_str =
  "exception Fail;"^
  "fun abs x = if x >= 0 then x else 0-x;"^
  "fun curcheck p ls ="^
  "  case ls of"^
  "    [] => ()"^
  "  | (l::ls) =>"^
  "  case p of (x,y) =>"^
  "  case l of (a,b) =>"^
  "  if a = x orelse b = y orelse abs(a-x)=abs(b-y) then raise Fail else curcheck (x,y) ls;"^
  "fun nqueens n cur ls ="^
  "  if cur >= n then ls"^
  "  else"^
  "    let fun find_queen y ="^
  "      if y >= n then raise Fail"^
  "      else"^
  "      (curcheck (cur,y) ls;nqueens n (cur+1) ((cur,y)::ls))"^
  "      handle Fail => find_queen (y+1)"^
  "    in"^
  "      find_queen 0"^
  "    end;"^
  "val foo = nqueens 29 0 [];"

val nqueens = check_prog nqueens_str;

val qsort_str =
  "fun part p l (l1,l2) ="^
  "  case l "^
  "  of [] => (l1,l2)"^
  "  |  h::rst => (if (p h)"^
  "                then (part p rst (h::l1,l2))"^
  "                else (part p rst (l1,h::l2)));"^
  "fun partition p l = part p l ([],[]);"^
  "fun append l1 l2 ="^
  "  case l1"^
  "  of [] => l2"^
  "  |  x::xs => (x::(append xs l2));"^
  "fun qsort r l ="^
  "  case l"^
  "  of [] => []"^
  "  |  h::t => (case (partition (fn y => (r y h)) t)"^
  "              of (l1,l2) => (append (qsort r l1) (append [h] (qsort r l2))));"^
  "fun mk_list n ="^
  "  if (n = 0)"^
  "  then []"^
  "  else (n::(mk_list (n - 1)));"^
  "fun use_qsort n ="^
  "  qsort (fn x => (fn y => (x <= y))) (append (mk_list n) (mk_list n));"^
  "val test = use_qsort 10000;"

val qsort = check_prog qsort_str;

val qsortimp_str =
  "fun swap i j arr ="^
  "  let val ti = Array.sub arr i"^
  "      val tj = Array.sub arr j"^
  "      val u = Array.update arr i tj in"^
  "        Array.update arr j ti"^
  "  end;"^
  "fun part_loop i j k arr ="^
  "  if i < j then"^
  "    (if Array.sub arr i <= k then"^
  "         part_loop (i+1) j k arr"^
  "     else"^
  "       let val u = swap i (j-1) arr in"^
  "         part_loop i (j-1) k arr"^
  "       end)"^
  "  else i;"^
  "fun inplace_partition b e arr ="^
  "    let val k = Array.sub arr b"^
  "        val i = part_loop (b+1) e k arr"^
  "        val u = swap b (i-1) arr in"^
  "           i-1"^
  "        end;"^
  "fun inplace_qsort b e arr ="^
  "    if b+1 < e then"^
  "      let val i = inplace_partition b e arr"^
  "          val u = inplace_qsort b i arr in"^
  "             inplace_qsort (i+1) e arr"^
  "      end"^
  "    else ();"^
  "fun initarr len arr n ="^
  "  if n = len then"^
  "    arr"^
  "  else"^
  "    let val u = Array.update arr n (len-n)"^
  "        val u = Array.update arr (n+len) (len-n) in"^
  "          initarr len arr (n+1)"^
  "        end;"^
  "fun mkarr n = initarr n (Array.array (n+n) 0) 0;"^
  "val foo = mkarr 20000"^
  "val test = inplace_qsort 0 40000 foo;"

val qsortimp = check_prog qsortimp_str;

val queue_str =
  "datatype 'a q = QUEUE of 'a list * 'a list;"^
  "val empty = QUEUE([],[]);"^
  "fun is_empty q ="^
  "  case q"^
  "  of QUEUE([],xs) => true"^
  "  |  _ => false;"^
  "fun reverse_aux l acc ="^
  "  case l"^
  "  of [] => acc"^
  "  |  x::xs => (reverse_aux xs (x::acc));"^
  "fun reverse xs = reverse_aux xs [];"^
  "fun checkf q ="^
  "  case q"^
  "  of QUEUE([],xs) => (QUEUE(reverse xs,[]))"^
  "  |  _ => q;"^
  "fun snoc q x = case q of QUEUE(f,r) => (checkf (QUEUE(f,x::r)));"^
  "fun head q = case q of QUEUE(x::f,r) => x;"^
  "fun tail q = case q of QUEUE(x::f,r) => (checkf (QUEUE(f,r)));"^
  "fun use_queue n q ="^
  "  if (n = 0)"^
  "  then q"^
  "  else (use_queue (n - 1) (tail (snoc (snoc q (n - 1)) (n - 1))));"^
  "fun run_queue n = head (use_queue n empty);"^
  "val test = run_queue 20000000;"

val queue = check_prog queue_str

val reverse_str =
  "fun reverse xs ="^
  "  let"^
  "    fun append xs ys ="^
  "      case xs of [] => ys"^
  "      | (x::xs) => x :: append xs ys;"^
  "    fun rev xs ="^
  "      case xs of [] => xs"^
  "      | (x::xs) => append (rev xs) [x]"^
  "  in"^
  "    rev xs"^
  "  end;"^
  "fun mk_list n ="^
  "  if (n = 0)"^
  "  then []"^
  "  else (n::(mk_list (n - 1)));"^
  "val test = reverse (mk_list 20000);"

val reverse = check_prog reverse_str

(* Run up to register allocator *)
fun compile_to_reg data_prog_def to_data_thm =
  let
    val cs = compilation_compset()
    val () =
      computeLib.extend_compset [
        computeLib.Extenders [
          arm6_targetLib.add_arm6_encode_compset,
          arm8_targetLib.add_arm8_encode_compset,
          mips_targetLib.add_mips_encode_compset,
          riscv_targetLib.add_riscv_encode_compset,
          x64_targetLib.add_x64_encode_compset],
        computeLib.Defs [
          arm6_backend_config_def, arm6_names_def,
          arm8_backend_config_def, arm8_names_def,
          mips_backend_config_def, mips_names_def,
          riscv_backend_config_def, riscv_names_def,
          x64_backend_config_def, x64_names_def,
          data_prog_def ]
      ] cs
    val eval = computeLib.CBV_CONV cs;
    fun parl f = parlist (!num_threads) (!chunk_size) f

    val (_,[conf_tm,prog_tm]) =
      to_data_thm |> concl |> lhs |> strip_comb

    val to_livesets_thm0 =
      ``to_livesets ^conf_tm ^prog_tm``
      |> (REWR_CONV to_livesets_def THENC
          RAND_CONV (REWR_CONV to_data_thm) THENC
          REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
          REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
          REWR_CONV LET_THM THENC BETA_CONV THENC
          REWR_CONV_BETA LET_THM THENC
          REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
          REWR_CONV LET_THM THENC
          PATH_CONV "rlrraraalralrarllr" eval THENC
          PATH_CONV"rlrraraalralralralralrar"
            (RATOR_CONV(RATOR_CONV(RAND_CONV eval)) THENC
             (FIRST_CONV (map REWR_CONV (CONJUNCTS bool_case_thm)))))
    val tm0 = to_livesets_thm0 |> rconc |> rand |> rand
    val thm0 = timez "data_to_word" eval tm0;

    val tm1 = to_livesets_thm0 |> rconc |> rand
    val (args,body) = tm1 |> rator |> rand |> dest_pabs
    val word_to_word_fn_def = zDefine`word_to_word_fn ^args = ^body`;
    val temp_defs = ["word_to_word_fn_def"];
    val word_to_word_fn_eq =
      word_to_word_fn_def
      |> SPEC_ALL
      |> PairRules.PABS args
      |> CONV_RULE(LAND_CONV PairRules.PETA_CONV)

    val word_to_word_fn = word_to_word_fn_eq|>concl|>lhs
    val word_prog = thm0 |> rconc |> listSyntax.dest_list |> #1
    val num_progs = length word_prog

    fun eval_fn i n p =
      let
        val tm = mk_comb(word_to_word_fn,p)
        val conv = RATOR_CONV(REWR_CONV word_to_word_fn_eq) THENC eval
      in
        conv tm
      end
    val ths = time_with_size thms_size "inst,ssa,two-reg (par)"
                (parl eval_fn) word_prog;
    val thm1 =
      tm1
      |> (RATOR_CONV(RAND_CONV(REWR_CONV(SYM word_to_word_fn_eq))) THENC
          RAND_CONV(REWR_CONV thm0) THENC map_ths_conv ths)
    in
    thm1 |> rconc
    end;
(*
    val word_prog0_def = mk_abbrev "word_prog0" (thm1 |> rconc)
    val temp_defs = (mk_abbrev_name"word_prog0")::temp_defs;

    val thm1' = thm1 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM word_prog0_def)))

    val to_livesets_thm1 =
      to_livesets_thm0
      |> CONV_RULE (RAND_CONV (
           RAND_CONV(REWR_CONV thm1') THENC
           BETA_CONV THENC
           REWR_CONV LET_THM))

    val tm2 = to_livesets_thm1 |> rconc |> rand
    val (args,body) = tm2 |> rator |> rand |> dest_pabs
    val clash_fn_def = zDefine`clash_fn ^args = ^body`;
    val temp_defs = (mk_abbrev_name"clash_fn")::temp_defs;
    val clash_fn_eq =
      clash_fn_def
      |> SPEC_ALL
      |> PairRules.PABS args
      |> CONV_RULE(LAND_CONV PairRules.PETA_CONV)
    val clash_fn = clash_fn_eq|>concl|>lhs

    val word_prog0 = thm1 |> rconc |> listSyntax.dest_list |> #1

    fun eval_fn i n p =
      let
        val tm = mk_comb(clash_fn,p)
        val conv = RATOR_CONV(REWR_CONV clash_fn_eq) THENC eval
      in
        conv tm
      end
    val ths = time_with_size thms_size "get_clash (par)"
                (parl eval_fn) word_prog0;
    val thm2 =
      tm2
      |> (RATOR_CONV(RAND_CONV(REWR_CONV(SYM clash_fn_eq))) THENC
          RAND_CONV(REWR_CONV word_prog0_def) THENC map_ths_conv ths)

    val to_livesets_thm =
      to_livesets_thm1
      |> CONV_RULE (RAND_CONV (
           RAND_CONV(REWR_CONV thm2) THENC
           BETA_CONV THENC
           PATH_CONV"lrlr"eval))
  in
    to_livesets_thm
  end; *)

fun compile backend_config_def name prog=
  let
    val prog_def = (mk_abbrev(String.concat[name,"_prog"])prog)
    val cs = compilation_compset()
    val conf_def = backend_config_def
    val data_prog_name = (!intermediate_prog_prefix) ^ "data_prog"
    val to_data_thm = compile_to_data cs conf_def prog_def data_prog_name
    val data_prog_def = definition(mk_abbrev_name data_prog_name)
    val bla = compile_to_reg data_prog_def to_data_thm
    in
      bla
    end

val compile_x64 = compile x64_backend_config_def

val benchmarks = map Option.valOf [btree,fib,foldl,nqueens,qsort,qsortimp,queue,reverse]
val names = ["btree","fib","foldl","nqueens","qsort","qsortimp","queue","reverse"]

val name = "btree";
val prog = Option.valOf btree;

val btree_tm = compile_x64 name prog;

(* Pretty print wordLang *)
open HolKernel Parse
open Portable smpp term_pp_types

fun wrap_sys sys = fn gravs => fn d => sys {gravs = gravs,depth = d, binderp=false}

(*Generic printer pass str,brk and blk*)
fun genPrint printFunc Gs B sys (ppfns:term_pp_types.ppstream_funs) (pg,lg,rg) d t =
  let
    open term_pp_types
    val (str,brk,blk) = (#add_string ppfns, #add_break ppfns,#ublock ppfns);
  in
    printFunc (wrap_sys sys) d t pg str brk blk
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

(*wordLang Seq *)
fun seqPrint sys d t pg str brk blk =
  let val (_,[p1,p2]) = strip_comb t
  in
    sys (pg,pg,pg) d p1 >>
    add_newline>>
    sys (pg,pg,pg) d p2
  end;

fun ifPrint sys d t pg str brk blk =
  let val (_,[cmp,r1,ri,p1,p2]) = strip_comb t
  in
    str"if " >> sys (pg,pg,pg) d cmp  >>str" ">> sys (pg,pg,pg) d r1 >> str" ">>sys (pg,pg,pg) d ri >>
    str" then" >>
    blk CONSISTENT 2 (
      add_newline>>
      sys (pg,pg,pg) d p1
    )>>add_newline>>
    str"else" >>
    blk CONSISTENT 2 (
      add_newline>>
      sys (pg,pg,pg) d p2
    )
  end;

fun recPrint sys d t pg str brk blk =
  let val ls = map snd (#2 (TypeBase.dest_record t))
  in
    str"( ">> List.foldr (fn (x,y) => sys(pg,pg,pg) d x>>str" ">>y) (str"") ls>>str")"
  end;

fun lsPrint sys d t pg str brk blk =
  let val ls = #1 (listSyntax.dest_list t)
  in
    str"[">>add_newline>>
    List.foldr (fn (x,y) => sys(pg,pg,pg) d x>>add_newline>>y) (str"") ls>>
    str"]"
  end;

fun print_to_file t tm =
let
  val [m,n,p] = pairSyntax.strip_pair tm
  val _ = print ("Evaluating: "^ term_to_string m ^"\n")
  val vals = rconc (EVAL`` get_heu ^p (LN,LN)``)
  val _ = TextIO.output(t,term_to_string tm)
  val _ = TextIO.output(t,"\n\n\n")
  val _ = TextIO.output(t,term_to_string vals)
  val _ = TextIO.output(t,"\n\n\n")
in
  ()
end;

fun print_all tms =
let
  val _ = temp_add_user_printer ("seqprint", ``wordLang$Seq p1 p2``,genPrint seqPrint)
  val _ = temp_add_user_printer ("ifprint", ``wordLang$If _ _ _ _ _ ``,genPrint ifPrint)
  val _ = temp_add_user_printer ("recprint", ``<|const:=_; reg:=_; mem:=_;fp:=_; other:=_;calls:=_ |>``,genPrint recPrint)
  val _ = temp_add_user_printer ("lsprint", ``xs:(num,heu_data) alist``,genPrint lsPrint)
  val _ = sptreeSyntax.temp_add_sptree_printer();
  val _ = set_trace "pp_avoids_symbol_merges" 0
  val _ = Globals.max_print_depth:= ~1
  val t = TextIO.openOut("dump.txt")
  val _ = List.app (fn tm => (print_to_file t tm; TextIO.flushOut t)) tms
  val _ = TextIO.closeOut t
  val _ = temp_remove_user_printer "ifprint"
  val _ = temp_remove_user_printer "seqprint"
  val _ = temp_remove_user_printer "recprint"
  val _ = temp_remove_user_printer "lsprint"
  val _ = Globals.max_print_depth:=20;
  val _ = set_trace "pp_avoids_symbol_merges" 1
  val _ = sptreeSyntax.remove_sptree_printer();
in
  ()
end;

val btree_ls = #1 (listSyntax.dest_list btree_tm);

val _ = print_all btree_ls;

val _ = export_theory ();
