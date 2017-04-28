open preamble
     parsingComputeLib inferenceComputeLib compilationLib
     basisProgTheory

(* TODO: Not too sure why parsingComputeLib has to be opened to get EVAL to
   work for parsing *)

val _ = new_theory "benchmark"

(* A simple test for the inferencer, precomputes the basis config, but doesn't store it as a constant *)
val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [inferenceComputeLib.add_inference_compset,
      basicComputeLib.add_basic_compset
      ],
     computeLib.Defs
      [basisProgTheory.basis_def]
    ] cmp
val inf_eval = computeLib.CBV_CONV cmp
val basis_config = dest_Success (rconc (inf_eval ``infertype_prog init_config basis``))

fun check_inf prog =
  inf_eval ``infertype_prog ^(basis_config) ^(prog)``

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
      if is_Success (rconc (check_inf parsed))
      then SOME(rconc (EVAL``basis ++ ^(parsed)``))
      else NONE
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

val benchmarks = map (fn (SOME x) => x) [nqueens,foldl,reverse,fib,qsort]
val names = ["nqueens","foldl","reverse","fib","qsort"]

fun write_asm [] = ()
  | write_asm ((name,(bytes,ffi_names))::xs) =
    (write_cake_S 1000 1000 (extract_ffi_names ffi_names)
       bytes ("cakeml/" ^ name ^ ".S") ;
    write_asm xs)

val benchmarks_compiled = map (to_bytes 3 ``x64_backend_config``) benchmarks

val benchmarks_bytes = map extract_bytes_ffis benchmarks_compiled

val _ = write_asm (zip names benchmarks_bytes);

val _ = map save_thm (zip names benchmarks_compiled);

(*
(*Turning down the register allocator*)
val benchmarks_compiled2 = map (to_bytes 0 ``x64_backend_config``) benchmarks
val benchmarks_bytes2 = map extract_bytes_ffis benchmarks_compiled2
val _ = write_asm (zip names benchmarks_bytes2);

(* Turn off clos optimizations*)
val clos_o0 = ``x64_backend_config.clos_conf with <|do_mti:=F;do_known:=F;do_call:=F;do_remove:=F|>``
val benchmarks_compiled3 = map (to_bytes 0 ``x64_backend_config with clos_conf:=^(clos_o0)``) benchmarks
val benchmarks_bytes3 = map extract_bytes_ffis benchmarks_compiled3
val _ = write_asm (zip names benchmarks_bytes3);

(* Turn off bvl_to_bvi optimzations ?*)
val bvl_o0 =  ``<|inline_size_limit := 0 ; exp_cut := 10000 ; split_main_at_seq := F|>``
val benchmarks_compiled4 = map (to_bytes 0 ``x64_backend_config with <|clos_conf:=^(clos_o0);bvl_conf:=^(bvl_o0)|>``) benchmarks
val benchmarks_bytes4 = map extract_bytes_ffis benchmarks_compiled4
val _ = write_asm (zip names benchmarks_bytes4);
*)

(*
val clos_o0 = ``x64_backend_config.clos_conf with <|do_mti:=F;do_known:=F;do_call:=F;do_remove:=F|>``
val clos_o1 = ``x64_backend_config.clos_conf with <|do_mti:=T;do_known:=F;do_call:=F;do_remove:=F|>``
val clos_o2 = ``x64_backend_config.clos_conf with <|do_mti:=T;do_known:=T;do_call:=F;do_remove:=F|>``
val clos_o3 = ``x64_backend_config.clos_conf with <|do_mti:=T;do_known:=T;do_call:=T;do_remove:=F|>``
val clos_o4 = ``x64_backend_config.clos_conf with <|do_mti:=T;do_known:=T;do_call:=T;do_remove:=T|>``

val benchmarks_o0 = map (to_bytes 3 ``x64_backend_config with clos_conf:=^(clos_o0)``) benchmarks
val benchmarks_o1 = map (to_bytes 3 ``x64_backend_config with clos_conf:=^(clos_o1)``) benchmarks
val benchmarks_o2 = map (to_bytes 3 ``x64_backend_config with clos_conf:=^(clos_o2)``) benchmarks
val benchmarks_o3 = map (to_bytes 3 ``x64_backend_config with clos_conf:=^(clos_o3)``) benchmarks
val benchmarks_o4 = map (to_bytes 3 ``x64_backend_config with clos_conf:=^(clos_o4)``) benchmarks

val benchmarks_o0_bytes = map extract_bytes_ffis benchmarks_o0
val benchmarks_o1_bytes = map extract_bytes_ffis benchmarks_o1
val benchmarks_o2_bytes = map extract_bytes_ffis benchmarks_o2
val benchmarks_o3_bytes = map extract_bytes_ffis benchmarks_o3
val benchmarks_o4_bytes = map extract_bytes_ffis benchmarks_o4

val _ = write_asm (zip (map (fn s => "o0_"^s)names) benchmarks_o0_bytes);
val _ = write_asm (zip (map (fn s => "o1_"^s)names) benchmarks_o1_bytes);
val _ = write_asm (zip (map (fn s => "o2_"^s)names) benchmarks_o2_bytes);
val _ = write_asm (zip (map (fn s => "o3_"^s)names) benchmarks_o3_bytes);
val _ = write_asm (zip (map (fn s => "o4_"^s)names) benchmarks_o4_bytes);
*)

val _ = export_theory ();
