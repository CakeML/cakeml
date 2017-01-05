open preamble astTheory wordLangTheory wordSemTheory tailrecTheory;
open mc_multiwordTheory set_sepTheory helperLib;

val good_dimindex_def = labPropsTheory.good_dimindex_def;

val _ = new_theory "word_bignum";


(* ---- This part will go into word_bignumScript.sml file ---- *)

(* syntax of a little language *)

val _ = Datatype `
  address = In1 | In2 | Out`

val _ = Datatype `
  prog = Skip
       | Assign num ('a wordLang$exp)
       | Delete (num list)
       | Seq prog prog
       | Load num num address
       | Store num num
       | If cmp num ('a reg_imm) prog prog
       | Swap
       | Add num num num ('a reg_imm) ('a reg_imm)
       | Sub num num num ('a reg_imm) ('a reg_imm)
       | Mul num num num num
       | Div num num num num num
       | Loop (num list) prog
       | Continue
       (* the following is only used by the semantics *)
       | LoopBody prog `


(* syntax helper funs *)

val Skip_tm = ``Skip:'a word_bignum$prog``
val Swap_tm = ``Swap:'a word_bignum$prog``
val Continue_tm = ``Continue:'a word_bignum$prog``

local val s = HolKernel.syntax_fns1 "word_bignum" in
  val (Delete_tm,mk_Delete,dest_Delete,is_Delete) = s "Delete"
end
local val s = HolKernel.syntax_fns2 "word_bignum" in
  val (Assign_tm,mk_Assign,dest_Assign,is_Assign) = s "Assign"
  val (Loop_tm,mk_Loop,dest_Loop,is_Loop) = s "Loop"
  val (Seq_tm,mk_Seq,dest_Seq,is_Seq) = s "Seq"
  val (Store_tm,mk_Store,dest_Store,is_Store) = s "Store"
end
local val s = HolKernel.syntax_fns3 "word_bignum" in
  val (Load_tm,mk_Load,dest_Load,is_Load) = s "Load"
end

local val s = HolKernel.syntax_fns1 "asm" in
  val (Imm_tm,mk_Imm,dest_Imm,is_Imm) = s "Imm"
  val (Reg_tm,mk_Reg,dest_Reg,is_Reg) = s "Reg"
end

val If_pat = ``word_bignum$If c r (ri:'a reg_imm) p1 p2``
fun dest_If tm = let
  val i = fst (match_term If_pat tm)
  val ts = helperLib.list_dest dest_comb If_pat
  in (subst i (el 2 ts),
      subst i (el 3 ts),
      subst i (el 4 ts),
      subst i (el 5 ts),
      subst i (el 6 ts)) end
fun mk_If (c,r,ri,p1,p2) = ``word_bignum$If ^c ^r ^ri ^p1 ^p2``;
fun is_If tm = can dest_If tm

(* generate deep embeddings *)

fun my_dest_let tm = let
  val (x,y) = pairSyntax.dest_anylet tm
  in if length x = 1 then (hd x,y) else fail() end

local
  val word_ty = ``:'a word``
in
  fun dest_reg v = let
    val (n,ty) = dest_var v
    val _ = ty = word_ty orelse fail()
    val n = String.substring(n,1,String.size(n)-1) |> string_to_int
    val n = numSyntax.term_of_int n
    in n end handle Subscript => fail()
end;

val binops = [(word_add_def,``asm$Add``),
              (word_sub_def,``asm$Sub``),
              (word_and_def,``asm$And``),
              (word_xor_def,``asm$Xor``),
              (word_or_def, ``asm$Or``)]
  |> map (fn (x,y) => (x |> SPEC_ALL |> concl |> dest_eq |> fst, y))

val shifts = [(word_lsr_def,``ast$Lsr``),
              (word_lsl_def,``ast$Lsl``),
              (word_asr_def,``ast$Asr``)]
  |> map (fn (x,y) => (x |> SPEC_ALL |> concl |> dest_eq |> fst, y))

fun get_exp x =
  (* Var *) let
  val n = dest_reg x
  in wordLangSyntax.mk_Var n end handle HOL_ERR _ =>
  (* Const *) let
  val _ = wordsSyntax.dest_n2w x
  in wordLangSyntax.mk_Const x end handle HOL_ERR _ =>
  (* Op *) let
  val (_,name) = first (fn (pat,_) => can (match_term pat) x) binops
  val x1 = get_exp (x |> rator |> rand)
  val x2 = get_exp (x |> rand)
  in wordLangSyntax.mk_Op(name,listSyntax.mk_list([x1,x2],type_of x1)) end
  handle HOL_ERR _ =>
  (* Shift *) let
  val (_,name) = first (fn (pat,_) => can (match_term pat) x) shifts
  val x1 = get_exp (x |> rator |> rand)
  val x2 = x |> rand
  in wordLangSyntax.mk_Shift(name,x1,``Nat ^x2``) end
  handle HOL_ERR _ =>
  (* ~ *) let
  val r = wordsSyntax.dest_word_1comp x
  in get_exp ``word_xor ^r (0w - 1w)`` end

val cmps = [(word_lo_def,``asm$Lower``),
            (word_lt_def,``asm$Less``),
            (GSYM w2n_11,``asm$Equal``)]
  |> map (fn (x,y) => (x |> SPEC_ALL |> concl |> dest_eq |> fst, y))

fun dest_reg_imm ri =
  mk_Reg (dest_reg ri) handle HOL_ERR _ =>
  if can wordsSyntax.dest_n2w ri then mk_Imm ri else fail()

fun get_guard b = (* Op *) let
  val (_,name) = first (fn (pat,_) => can (match_term pat) b) cmps
  val x1 = dest_reg (b |> rator |> rand)
  val x2 = dest_reg_imm (b |> rand)
  in (name,x1,x2) end handle HOL_ERR _ => let
  val _ = can (match_term ``(w && n2w n) = 0w:'a word``) b orelse fail()
  val x1 = b |> rator |> rand |> rator |> rand
  val x2 = b |> rator |> rand |> rand
  in (``asm$Test``,dest_reg x1,dest_reg_imm x2) end

local
  val LUPDATE_pat = ``LUPDATE a (w2n (r:'a word)) (zs:'b list)``
in
  fun dest_lupdate_let tm = let
    val (rest,r) = dest_let tm
    val (v,body) = dest_abs rest
    val _ = (v = rand r) orelse fail ()
    val _ = can (match_term LUPDATE_pat) r orelse fail()
    val x = r |> rator |> rator |> rand
    val y = r |> rator |> rand |> rand
    in (x,y,body) end
end

local
  val EL_pat = ``EL (w2n (r:'a word)) (zs:'b list)``
in
  fun dest_el_let tm = let
    val (rest,r) = dest_let tm
    val (v,body) = dest_abs rest
    val _ = can (match_term EL_pat) r orelse fail()
    val a = r |> rand |> dest_var |> fst
    val a = if a = "xs" then ``In1`` else
            if a = "ys" then ``In2`` else
            if a = "zs" then ``Out`` else fail()
    val y = r |> rator |> rand |> rand
    in (v,y,a,body) end
end

local
  val add_pat = ``single_add_word r0 r1 ri``
  val sub_pat = ``single_sub_word r0 r1 ri``
  fun dest_single_add_sub_let pat tm = let
    val (rest,r) = dest_let tm
    val (v,body) = dest_pabs rest
    val _ = can (match_term pat) r orelse fail()
    val (a1,a2) = pairSyntax.dest_pair v
    val a1 = dest_reg a1
    val a2 = dest_reg a2
    val args = snd (strip_comb r)
    val r1 = dest_reg (el 1 args)
    val r2 = dest_reg_imm (el 2 args)
    val r3 = dest_reg_imm (el 3 args)
    in (a1,a2,r1,r2,r3,body) end
in
  val dest_single_add_let = dest_single_add_sub_let add_pat
  val dest_single_sub_let = dest_single_add_sub_let sub_pat
end

local
  val mul_pat = ``single_mul r0 r2 0w``
in
  fun dest_single_mul_let tm = let
    val (rest,r) = dest_let tm
    val (v,body) = dest_pabs rest
    val _ = can (match_term mul_pat) r orelse fail()
    val (a1,a2) = pairSyntax.dest_pair v
    val a1 = dest_reg a1
    val a2 = dest_reg a2
    val args = snd (strip_comb r)
    val r1 = dest_reg (el 1 args)
    val r2 = dest_reg (el 2 args)
    in (a1,a2,r1,r2,body) end
end

local
  val div_pat = ``single_div r2 r0 r1``
in
  fun dest_single_div_let tm = let
    val (rest,r) = dest_let tm
    val (v,body) = dest_pabs rest
    val _ = can (match_term div_pat) r orelse fail()
    val (a1,a2) = pairSyntax.dest_pair v
    val a1 = dest_reg a1
    val a2 = dest_reg a2
    val args = snd (strip_comb r)
    val r1 = dest_reg (el 1 args)
    val r2 = dest_reg (el 2 args)
    val r3 = dest_reg (el 3 args)
    in (a1,a2,r1,r2,r3,body) end
end

fun get_let tm =
  (* Load *)
  let
    val (r,i,a,rest) = dest_el_let tm
  in (mk_Load(dest_reg r, dest_reg i, a),rest) end handle HOL_ERR _ =>
  (* Store *)
  let
    val (r,i,rest) = dest_lupdate_let tm
  in (mk_Store(dest_reg r, dest_reg i),rest) end handle HOL_ERR _ =>
  (* Assign *)
  let
    val ((v,x),rest) = my_dest_let tm
    val n = dest_reg v
    val e = get_exp x
  in (mk_Assign(n,e),rest) end handle HOL_ERR _ =>
  (* Swap *)
  let
    val ((v,x),rest) = my_dest_let tm
    val _ = pairSyntax.is_pair x orelse fail()
  in (``Swap``,rest) end handle HOL_ERR _ =>
  (* Add *)
  let
    val (a1,a2,r1,r2,r3,rest) = dest_single_add_let tm
  in (``Add ^a1 ^a2 ^r1 ^r2 ^r3``,rest) end handle HOL_ERR _ =>
  (* Sub *)
  let
    val (a1,a2,r1,r2,r3,rest) = dest_single_sub_let tm
  in (``Sub ^a1 ^a2 ^r1 ^r2 ^r3``,rest) end handle HOL_ERR _ =>
  (* Mul *)
  let
    val (a1,a2,r1,r2,rest) = dest_single_mul_let tm
  in (``Mul ^a1 ^a2 ^r1 ^r2``,rest) end handle HOL_ERR _ =>
  (* Div *)
  let
    val (a1,a2,r1,r2,r3,rest) = dest_single_div_let tm
  in (``Div ^a1 ^a2 ^r1 ^r2 ^r3``,rest) end handle HOL_ERR _ =>
  fail ()

val code_defs = ref TRUTH;
val prev_trans = ref ([]: (term * term) list);

exception UnableToTranslate of string;

val def = mc_mul_zero_def
val tm = def |> concl |> rand
val inp = def |> concl |> rator |> rand |> rand

fun get_full_prog inp tm = let
  val immediate_deps = ref ([]:term list);
  val ret_tm = ref Skip_tm;
  val cont_tm = ref Continue_tm;
  val ret_vars = ref ([]:term list);
  val cont_vars = ref ([]:term list);
  (* main function *)
  fun get_prog tm =
    (* return *)
    if is_var tm orelse pairSyntax.is_pair tm
    then (ret_vars := free_vars tm; !ret_tm)
    else
    (* let *) let
    val (x,rest) = get_let tm
    in mk_Seq(x,get_prog rest) end handle HOL_ERR _ =>
    (* previous translation *) let
    val ((v,x),rest) = my_dest_let tm
    val f = x |> repeat rator
    val (_,code) = first (fn (x,y) => same_const x f) (!prev_trans)
    val _ = (immediate_deps := code :: (!immediate_deps))
    in mk_Seq(code,get_prog rest) end handle HOL_ERR _ =>
    (* If *) let
    val (b,t1,t2) = dest_cond tm
    val (x1,x2,x3) = get_guard b
    in mk_If(x1,x2,x3,get_prog t1,get_prog t2) end handle HOL_ERR _ =>
    if is_const (rator tm) andalso (is_var (rand tm) orelse is_pair (rand tm))
    then (cont_vars := free_vars tm; !cont_tm)
    else let
      val ((v,x),rest) = my_dest_let tm
      val str = repeat rator x |> dest_const |> fst
      in raise UnableToTranslate str end
      handle HOL_ERR e =>
        (print "Unable to translate\n\n";
         print_term tm;
         print "\n\n";
         raise HOL_ERR e)
  (* compute deps *)
  val init_prog = get_prog tm
  (* compute what vars are deleted or assigned *)
  val x = !code_defs |> CONJUNCTS
             |> filter (fn tm => mem (lhs (concl tm)) (!immediate_deps)
                                 handle HOL_ERR _ => true)
             |> LIST_CONJ |> CONJ (REFL init_prog) |> concl
  fun is_delete tm =
    can (match_term ``(Delete n):'a prog``) tm
  val Add_tm = ``(Add n1 n2):num -> α reg_imm -> α reg_imm -> α prog``
  val Sub_tm = ``(Sub n1 n2):num -> α reg_imm -> α reg_imm -> α prog``
  val Mul_tm = ``(Mul n1 n2):num -> num -> α prog``
  val Div_tm = ``(Div n1 n2):num -> num -> num -> α prog``
  fun is_assign tm =
    can (match_term ``(Assign n):α wordLang$exp -> α prog``) tm orelse
    can (match_term ``(Load n):num -> address -> α prog``) tm orelse
    can (match_term Add_tm) tm orelse can (match_term (rator Add_tm)) tm orelse
    can (match_term Sub_tm) tm orelse can (match_term (rator Sub_tm)) tm orelse
    can (match_term Mul_tm) tm orelse can (match_term (rator Mul_tm)) tm orelse
    can (match_term Div_tm) tm orelse can (match_term (rator Div_tm)) tm
  fun f tm = dest_reg tm handle HOL_ERR _ => tm
  val ds = Lib.mk_set ((find_terms is_assign x |> map rand) @
                       (find_terms is_delete x
                            |> map (fst o listSyntax.dest_list o rand)
                            |> flatten) @
                       filter (not o is_var) (map f (free_vars inp)))
  fun add_dels [] tm = tm
    | add_dels vs tm = mk_Seq (mk_Delete (listSyntax.mk_list(vs,type_of (hd vs))), tm)
  val _ = (ret_tm := add_dels (Lib.set_diff ds (map f (!ret_vars))) Skip_tm)
  val cont_dels = (Lib.set_diff ds (map f (!cont_vars)))
  val _ = (cont_tm := add_dels cont_dels Continue_tm)
  in (listSyntax.mk_list(cont_dels,``:num``),get_prog tm) end

fun to_deep def = let
  (* produce deep embedding *)
  val f = def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
  val tm = def |> SPEC_ALL |> concl |> rand
  val inp = def |> SPEC_ALL |> concl |> rator |> rand |> rand
  val is_rec = can (find_term (fn tm => (tm = f))) tm
  fun loop () =
    get_full_prog inp tm
    handle UnableToTranslate str =>
      (to_deep (find (str ^ "_def") |> hd |> snd |> fst);
       loop ())
  val (dels,deep) = loop ()
  val deep = if is_rec then mk_Loop (dels,deep) else deep
  (* store deep embedding *)
  val name = mk_var((f |> dest_const |> fst) ^ "_code", type_of deep)
  val code_def = Define `^name = ^deep`
  val code_const = code_def |> concl |> dest_eq |> fst
  val _ = (code_defs := CONJ code_def (!code_defs))
  val _ = (prev_trans := (f,code_const) :: (!prev_trans))
  in code_def end
  handle HOL_ERR e =>
    (print ("Failed at " ^ term_to_string
       (def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator) ^ "\n");
     raise (HOL_ERR e))

(*
val tm = def |> SPEC_ALL |> concl |> rand
*)

val def = mc_cmp_def |> to_deep
val def = mc_compare_def |> to_deep
val def = mc_idiv_def |> to_deep
val def = mc_iadd_def |> to_deep
val def = mc_imul_def |> to_deep
val def = mc_iop_def |> to_deep

val all_code_defs = save_thm("all_code_defs", REWRITE_RULE [] (!code_defs));


(* compiler into wordLang *)

val has_compiled_def = Define `
  has_compiled code (n,code_list) =
    case ALOOKUP code_list code of
    | NONE => INR (n:num)
    | SOME (index,word_code) => INL (index:num)`;

val next_def = Define `
  next (n,code_list) = (n+1n,code_list)`

val install_def = Define `
  install c (n,code_list) = (n,c::code_list)`

(*
val ShiftVar_def = Define `
  ShiftVar sh v n =
    if n = 0 then v else
    if dimindex (:'a) <= n then
      if sh = Asr then Shift sh v (Nat (dimindex (:'a) - 1)) else Const 0w
    else (Shift sh v (Nat n)):'a wordLang$exp`
*)

val compile_exp_def = Define `
  compile_exp (Op b [x1;x2]) = Op b [compile_exp x1; compile_exp x2] /\
  compile_exp (Var n) = Lookup (Temp (n2w n)) /\
  compile_exp (Const w) = Const w /\
  compile_exp (Shift sh x (Nat na)) = Shift sh (compile_exp x) (Nat na) /\
  compile_exp _ = Const 0w`

val TempIn1_def = Define `TempIn1 = Temp 31w`
val TempIn2_def = Define `TempIn2 = Temp 30w`
val TempOut_def = Define `TempOut = Temp 29w`

val SeqTemp_def = Define `
  SeqTemp i r p = Seq (wordLang$Assign i (Lookup (Temp (n2w r)))) p`;

val SeqTempImm_def = Define `
  SeqTempImm i (Reg r) p = SeqTemp i r p /\
  SeqTempImm i (Imm w) p = Seq (wordLang$Assign i (Const w)) p`;

val SeqTempImmNot_def = Define `
  SeqTempImmNot i (Reg r) p =
    SeqTemp i r (Seq (Assign i (Op Xor [Var i; Const (~0w)])) p) /\
  SeqTempImmNot i (Imm w) p = Seq (wordLang$Assign i (Const (~w))) p`;

val SeqIndex_def = Define `
  SeqIndex i r arr p =
    let t = (case arr of Out => TempOut | In2 => TempIn2 | In1 => TempIn1) in
      Seq (Assign i (Op Add [Lookup t;
           Shift Lsl (Lookup (Temp (n2w r))) (Nat (shift (:'a)))])) p
              :'a wordLang$prog`

val compile_def = Define `
  (compile n l i cs Skip = (wordLang$Skip,l,i,cs)) /\
  (compile n l i cs Continue = (Call NONE (SOME n) [0] NONE,l,i,cs)) /\
  (compile n l i cs (Loop vs body) =
     case has_compiled body cs of
     | INL existing_index =>
         (Call (SOME (i,LS (),Skip,n,l)) (SOME existing_index) [] NONE,l+1,i+1,cs)
     | INR new_index =>
         let (new_code,a,b,cs) = compile new_index 1 1 (next cs) body in
           (Call (SOME (i,LS (),Skip,n,l)) (SOME new_index) [] NONE,l+1,i+1,
            install (body,new_index,Seq new_code (Return 0 0)) cs)) /\
  (compile n l i cs (LoopBody b) = compile n l i cs b) /\
  (compile n l i cs (Seq p1 p2) =
     let (p1,l,i,cs) = compile n l i cs p1 in
     let (p2,l,i,cs) = compile n l i cs p2 in
       (Seq p1 p2,l,i,cs)) /\
  (compile n l i cs (If t r ri p1 p2) =
     let (p1,l,i,cs) = compile n l i cs p1 in
     let (p2,l,i,cs) = compile n l i cs p2 in
       case ri of
       | Reg r2 => (SeqTemp i r (SeqTemp (i+1) r2 (If t i (Reg (i+1)) p1 p2)),
                    l,i+2,cs)
       | Imm im => (SeqTemp i r (If t i ri p1 p2),l,i+1,cs)) /\
  (compile n l i cs (Assign j e) =
     (Seq (Assign i (compile_exp e)) (Set (Temp (n2w j)) (Var i)),l,i+1,cs)) /\
  (compile n l i cs (Delete _) = (Skip:'a wordLang$prog,l,i,cs)) /\
  (compile n l i cs Swap =
     (Seq (Assign i (Lookup (TempIn1)))
     (Seq (Set (TempIn1) (Lookup (TempIn2)))
          (Set (TempIn2) (Var i))),l,i+1,cs)) /\
  (compile n l i cs (Store r1 r2) =
     (SeqTemp i r1
     (SeqIndex (i+1) r2 Out
        (Store (Var (i+1)) i)),l,i+2,cs)) /\
  (compile n l i cs (Load r1 r2 arr) =
     (SeqIndex i r2 arr
     (Seq (Assign (i+1) (Load (Var i)))
          (Set (Temp (n2w r1)) (Var (i+1)))),l,i+2,cs)) /\
  (compile n l i cs (Add r0 r1 r2 r3 r4) =
     (SeqTempImm (i+4) r4 (SeqTempImm (i+3) r3 (SeqTemp (i+2) r2
     (Seq (Inst (Arith (AddCarry (i+1) (i+2) (i+3) (i+4))))
     (Seq (Set (Temp (n2w r0)) (Var (i+1)))
          (Set (Temp (n2w r1)) (Var (i+4))))))),l,i+5,cs)) /\
  (compile n l i cs (Sub r0 r1 r2 r3 r4) =
     (SeqTempImm (i+4) r4 (SeqTempImmNot (i+3) r3 (SeqTemp (i+2) r2
     (Seq (Inst (Arith (AddCarry (i+1) (i+2) (i+3) (i+4))))
     (Seq (Set (Temp (n2w r0)) (Var (i+1)))
          (Set (Temp (n2w r1)) (Var (i+4))))))),l,i+5,cs)) /\
  (compile n l i cs (Mul r0 r1 r2 r3) =
     (SeqTemp (i+3) r3 (SeqTemp (i+2) r2
     (Seq (Inst (Arith (LongMul (i+0) (i+1) (i+2) (i+3))))
     (Seq (Set (Temp (n2w r1)) (Var (i+0)))
          (Set (Temp (n2w r0)) (Var (i+1)))))),l,i+4,cs)) /\
  (compile n l i cs (Div r0 r1 r2 r3 r4) =
     (SeqTemp (i+4) r4 (SeqTemp (i+3) r3 (SeqTemp (i+2) r2
     (Seq (Inst (Arith (LongDiv (i+0) (i+1) (i+2) (i+3) (i+4))))
     (Seq (Set (Temp (n2w r0)) (Var (i+0)))
          (Set (Temp (n2w r1)) (Var (i+1))))))),l,i+5,cs)) /\
  (compile n l i cs _ = (Skip,l,i,cs))`

val _ = (max_print_depth := 25);

val mc_iop_compile_def = Define `
  mc_iop_compile n =
    let (x1,_,_,(_,cs)) = compile n 1 1 (n+1,[]) mc_iop_code in
      (n,1n,Seq x1 (Return 0 0)) :: MAP (\(x,y,z). (y,1,z)) cs`

val mc_iop_compile_eq = save_thm("mc_iop_compile_eq",
  EVAL ``mc_iop_compile n`` |> SIMP_RULE std_ss [GSYM ADD_ASSOC]);


(* ---- This part will go into word_bignumProofScript.sml file ---- *)

(* semantics of the little language *)

val _ = Datatype `
  state = <| regs : num |-> 'a word
           ; arrays : address -> ('a word) list
           ; clock : num
           |>`

val eval_exp_def = Define `
  eval_exp s (Const w) = w /\
  eval_exp s (Var v) = s.regs ' v /\
  eval_exp s (Op Add [x1;x2]) = eval_exp s x1 + eval_exp s x2 /\
  eval_exp s (Op Sub [x1;x2]) = eval_exp s x1 - eval_exp s x2 /\
  eval_exp s (Op And [x1;x2]) = word_and (eval_exp s x1) (eval_exp s x2) /\
  eval_exp s (Op Or [x1;x2]) = word_or (eval_exp s x1) (eval_exp s x2) /\
  eval_exp s (Op Xor [x1;x2]) = word_xor (eval_exp s x1) (eval_exp s x2) /\
  eval_exp s (Shift Lsl x (Nat n)) = eval_exp s x << n /\
  eval_exp s (Shift Asr x (Nat n)) = eval_exp s x >> n /\
  eval_exp s (Shift Lsr x (Nat n)) = eval_exp s x >>> n`

val eval_exp_pre_def = Define `
  (eval_exp_pre s (Const w) <=> T) /\
  (eval_exp_pre s (Var v) <=> v IN FDOM s.regs) /\
  (eval_exp_pre s (Op _ [x;y]) <=> eval_exp_pre s x /\ eval_exp_pre s y) /\
  (eval_exp_pre s (Shift sh x (Nat n)) <=> eval_exp_pre s x /\ n = 1) /\
  (eval_exp_pre s _ <=> F)`

val eval_ri_pre_def = Define `
  (eval_ri_pre s (Reg r) <=> eval_exp_pre (s:'a state) ((Var r):'a wordLang$exp)) /\
  (eval_ri_pre s (Imm (w:'a word)) <=> T)`;

val eval_ri_def = Define `
  eval_ri s (Reg r) = eval_exp s (Var r) /\
  eval_ri s (Imm w) = w`

val dec_clock_def = Define `
  dec_clock s = s with clock := s.clock - 1`;

val reg_write_def = Define `
  reg_write v NONE (s:'a state) = s with regs := s.regs \\ v /\
  reg_write n (SOME v) s = s with regs := s.regs |+ (n,v)`;

val delete_vars_def = Define `
  delete_vars [] s = s /\
  delete_vars (v::vs) s = reg_write v NONE (delete_vars vs s)`

val array_write_def = Define `
  array_write n v s = s with arrays := (n =+ v) s.arrays`;

val clock_write_def = Define `
  clock_write l s = s with clock := l`;

val (eval_rules,eval_ind,raw_eval_cases) = Hol_reln `
  (!s. Eval s Skip (INR (s:'a state))) /\
  (!s. Eval s Continue (INL s)) /\
  (!vs s. Eval s (Delete vs) (INR (delete_vars vs (s:'a state)))) /\
  (!s x n.
     eval_exp_pre s x ==>
     Eval s (Assign n x) (INR (reg_write n (SOME (eval_exp s x)) s))) /\
  (!s1 s2 s3 p1 p2.
     Eval s1 p1 (INR s2) /\ Eval s2 p2 s3 ==>
     Eval s1 (Seq p1 p2) s3) /\
  (!s1 c r ri p1 p2 s2.
     r IN FDOM s1.regs /\ eval_ri_pre s1 ri /\
     Eval s1 (if word_cmp c (eval_exp s1 (Var r)) (eval_ri s1 ri)
              then p1 else p2) s2 ==>
     Eval s1 (If c r ri p1 p2) s2) /\
  (!s r i a w.
     (FLOOKUP s.regs i = SOME w) /\
     w2n w < LENGTH (s.arrays a) ==>
     Eval s (Load r i a) (INR (reg_write r (SOME (EL (w2n w) (s.arrays a))) s))) /\
  (!s r i w wr.
     (FLOOKUP s.regs i = SOME w) /\ (FLOOKUP s.regs r = SOME wr) /\
     w2n w < LENGTH (s.arrays Out) ==>
     Eval s (Store r i) (INR (array_write Out (LUPDATE wr (w2n w) (s.arrays Out)) s))) /\
  (!s.
     Eval s Swap (INR (array_write In1 (s.arrays In2)
                      (array_write In2 (s.arrays In1) s)))) /\
  (!s r1 r2.
     n3 IN FDOM s.regs /\ eval_ri_pre s n4 /\ eval_ri_pre s n5 /\
     (eval_ri s n5 <> 0w ==> eval_ri s n5 = 1w) /\ n1 <> n2 /\
     (single_add_word (s.regs ' n3) (eval_ri s n4) (eval_ri s n5) = (r1,r2)) ==>
     Eval s (Add n1 n2 n3 n4 n5)
      (INR (reg_write n1 (SOME r1) (reg_write n2 (SOME r2) s)))) /\
  (!s n1 n2 n3 n4 n5 r1 r2.
     n3 IN FDOM s.regs /\ eval_ri_pre s n4 /\ eval_ri_pre s n5 /\
     (eval_ri s n5 <> 0w ==> eval_ri s n5 = 1w) /\ n1 <> n2 /\
     (single_sub_word (s.regs ' n3) (eval_ri s n4) (eval_ri s n5) = (r1,r2)) ==>
     Eval s (Sub n1 n2 n3 n4 n5)
      (INR (reg_write n1 (SOME r1) (reg_write n2 (SOME r2) s)))) /\
  (!s n1 n2 n3 n4.
     n3 IN FDOM s.regs /\ n4 IN FDOM s.regs /\ n1 <> n2 ==>
     Eval s (Mul n1 n2 n3 n4)
      (INR (reg_write n1 (SOME (FST (single_mul (s.regs ' n3) (s.regs ' n4) 0w)))
           (reg_write n2 (SOME (SND (single_mul (s.regs ' n3) (s.regs ' n4) 0w))) s)))) /\
  (!s n1 n2 n3 n4 n5.
     n3 IN FDOM s.regs /\ n4 IN FDOM s.regs /\ n5 IN FDOM s.regs /\ n1 <> n2 /\
     single_div_pre (s.regs ' n3) (s.regs ' n4) (s.regs ' n5) ==>
     Eval s (Div n1 n2 n3 n4 n5)
      (INR (reg_write n1 (SOME (FST (single_div (s.regs ' n3) (s.regs ' n4) (s.regs ' n5))))
           (reg_write n2 (SOME (SND (single_div (s.regs ' n3) (s.regs ' n4) (s.regs ' n5)))) s)))) /\
  (!s1 p vs s2.
     Eval (delete_vars vs (dec_clock s1)) (LoopBody p) (INR s2) /\ s1.clock <> 0 ==>
     Eval s1 (Loop vs p) (INR s2)) /\
  (!s1 p s2.
     Eval s1 p (INR s2) ==>
     Eval s1 (LoopBody p) (INR s2)) /\
  (!s1 s2 s3 p.
     Eval s1 p (INL s2) /\ s2.clock <> 0 /\
     Eval (dec_clock s2) (LoopBody p) (INR s3) ==>
     Eval s1 (LoopBody p) (INR s3))`

val eval_cases =
  map (SIMP_CONV (srw_ss()) [Once raw_eval_cases])
    [``Eval s1 Skip s2``,
     ``Eval s1 Continue s2``,
     ``Eval s1 (Delete vs) s2``,
     ``Eval s1 (Seq p1 p2) s2``,
     ``Eval s1 (Assign n x) s2``,
     ``Eval s1 (If c r ri p1 p2) s2``,
     ``Eval s1 (Load r i a) s2``,
     ``Eval s1 (Store r i) s2``,
     ``Eval s1 Swap s2``,
     ``Eval s1 (Add r1 r2 r3 r4 r5) s2``,
     ``Eval s1 (Sub r1 r2 r3 r4 r5) s2``,
     ``Eval s1 (Mul r1 r2 r3 r4) s2``,
     ``Eval s1 (Div r1 r2 r3 r4 r5) s2``,
     ``Eval s1 (Loop vs p) s2``,
     ``Eval s1 (LoopBody p) s2``] |> LIST_CONJ;


(* verification of compiler to wordLang *)

val array_rel_def = Define `
  array_rel arr v1 v2 v3 m dm frame =
    ?a1 a2 a3 rest1 rest2.
      v1 = SOME (Word a1) /\
      v2 = SOME (Word a2) /\
      v3 = SOME (Word a3) /\
      (word_list a1 (MAP Word (arr In1)) *
       word_list a3 (MAP Word (arr Out)) * rest1) (fun2set (m,dm)) /\
      (word_list a2 (MAP Word (arr In2)) *
       word_list a3 (MAP Word (arr Out)) * rest2) (fun2set (m,dm)) /\
      (word_list a3 (MAP Word (arr Out)) * frame) (fun2set (m,dm))`

val code_subset_def = Define `
  code_subset (n1,cs1) (n2,cs2) <=>
    !n v. ALOOKUP cs1 n = SOME v ==> ALOOKUP cs2 n = SOME v`;

val code_rel_def = Define `
  code_rel cs code <=>
    !prog n p2.
       ALOOKUP (SND cs) prog = SOME (n,p2) ==>
       ?cs1 l2 i2 cs2.
         compile n 1 1 cs1 prog = (p2,l2,i2,cs2) /\
         lookup n code = SOME (1n,Seq p2 (Return 0 0)) /\
         code_subset cs2 cs`

val _ = temp_overload_on("max_var_name",``25n``);

val state_rel_def = Define `
  state_rel s t cs t0 frame <=>
    (* clock related *)
    s.clock = t.clock /\
    (* array related *)
    array_rel s.arrays (FLOOKUP t.store TempIn1)
                       (FLOOKUP t.store TempIn2)
                       (FLOOKUP t.store TempOut) t.memory t.mdomain frame /\
    (* regs related *)
    (!a v.
       FLOOKUP s.regs a = SOME v ==>
       a < 25 /\
       FLOOKUP t.store (Temp (n2w a)) = SOME (Word v)) /\
    (* code assumption *)
    code_rel cs t.code /\
    (* rest same as original *)
    t0.gc_fun = t.gc_fun /\
    t0.handler = t.handler /\
    t0.termdep = t.termdep /\
    t0.code = t.code /\
    t0.be = t.be /\
    t0.ffi = t.ffi /\
    (!n. (!r. n <> Temp r) ==> FLOOKUP t.store n = FLOOKUP t0.store n)`

val state_rel_delete_vars = prove(
  ``s1.arrays = s2.arrays /\ s1.clock = s2.clock /\
    s2.regs SUBMAP s1.regs ==>
    state_rel s1 t1 cs t0 frame ==>
    state_rel s2 t1 cs t0 frame``,
  fs [state_rel_def] \\ rw []
  \\ fs [SUBMAP_DEF,FLOOKUP_DEF]
  \\ metis_tac []);

val state_rel_delete_vars = prove(
  ``!vs. state_rel s1 t1 cs t0 frame ==>
         state_rel (delete_vars vs s1) t1 cs t0 frame``,
  strip_tac
  \\ match_mp_tac state_rel_delete_vars
  \\ Induct_on `vs` \\ fs [delete_vars_def,reg_write_def]
  \\ fs [SUBMAP_DEF,FDOM_DOMSUB,DOMSUB_FAPPLY_THM]);

val exp_ok_def = Define `
  (exp_ok (Const _) <=> T) /\
  (exp_ok (Var i) <=> i < max_var_name) /\
  (exp_ok (Op _ [x;y]) <=> exp_ok x /\ exp_ok y) /\
  (exp_ok (Shift sh e n) <=> exp_ok e) /\
  (exp_ok _ <=> F)`;

val syntax_ok_aux_def = Define `
  syntax_ok_aux (Loop vs body) = syntax_ok_aux body /\
  syntax_ok_aux (LoopBody body) = F /\
  (syntax_ok_aux (Seq p1 p2) <=> syntax_ok_aux p1 /\ syntax_ok_aux p2) /\
  (syntax_ok_aux (Assign t1 e) <=> t1 < max_var_name /\ exp_ok e) /\
  (syntax_ok_aux (Load t1 t2 _) <=> t1 < max_var_name /\ t2 < max_var_name) /\
  (syntax_ok_aux (Store t1 t2) <=> t1 < max_var_name /\ t2 < max_var_name) /\
  (syntax_ok_aux (If t1 t2 t3 p1 p2) <=>
     t2 < max_var_name /\ (!r. t3 = Reg r ==> r < max_var_name) /\
     syntax_ok_aux p1 /\ syntax_ok_aux p2) /\
  (syntax_ok_aux (Add n1 n2 n3 n4 n5) <=>
     n1 < max_var_name /\ n2 < max_var_name /\ n3 < max_var_name /\
     (!r. n4 = Reg r ==> r < max_var_name) /\
     (!r. n5 = Reg r ==> r < max_var_name)) /\
  (syntax_ok_aux (Sub n1 n2 n3 n4 n5) <=>
     n1 < max_var_name /\ n2 < max_var_name /\ n3 < max_var_name /\
     (!r. n4 = Reg r ==> r < max_var_name) /\
     (!r. n5 = Reg r ==> r < max_var_name)) /\
  (syntax_ok_aux (Mul n1 n2 n3 n4) <=>
     n1 < max_var_name /\ n2 < max_var_name /\
     n3 < max_var_name /\ n4 < max_var_name) /\
  (syntax_ok_aux (Div n1 n2 n3 n4 n5) <=>
     n1 < max_var_name /\ n2 < max_var_name /\
     n3 < max_var_name /\ n4 < max_var_name /\ n5 < max_var_name) /\
  syntax_ok_aux _ = T`;

val syntax_ok_def = Define `
  syntax_ok (LoopBody body) = syntax_ok_aux body /\
  syntax_ok p = syntax_ok_aux p`

val evaluate_Seq_Seq = store_thm("evaluate_Seq_Seq",
  ``!p1 p2 p3 t1.
      wordSem$evaluate (Seq p1 (Seq p2 p3),t1) = evaluate (Seq (Seq p1 p2) p3,t1)``,
  Induct
  \\ fs [evaluate_def] \\ rw []
  \\ every_case_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ rw []);

val env_to_list_insert_0_LN = prove(
  ``env_to_list (insert 0 ret_val LN) p = ([0,ret_val],(\n. p (n+1)))``,
  fs [env_to_list_def,toAList_def,Once insert_def,foldi_def]
  \\ fs [QSORT_DEF,PARTITION_DEF,PART_DEF]
  \\ fs [list_rearrange_def] \\ rw []
  \\ fs [BIJ_DEF,EVAL ``count 1``,INJ_DEF,SURJ_DEF]);

val code_subset_refl = prove(
  ``!c1. code_subset c1 c1``,
  fs [code_subset_def,FORALL_PROD]);

val code_subset_trans = prove(
  ``!c1 c2 c3. code_subset c1 c2 /\ code_subset c2 c3 ==> code_subset c1 c3``,
  fs [code_subset_def,FORALL_PROD]);

val compile_IMP_code_subset = prove(
  ``!prog n l i cs p1 l1 i1 cs1.
      compile n l i cs prog = (p1,l1,i1,cs1) ==> code_subset cs cs1 /\ i <= i1``,
  Induct
  \\ TRY (fs [compile_def,code_subset_refl] \\ NO_TAC)
  \\ fs [compile_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [] \\ rw [])
  \\ res_tac
  \\ imp_res_tac code_subset_trans
  \\ every_case_tac \\ fs [code_subset_refl]
  \\ pairarg_tac \\ fs []
  \\ Cases_on `cs`
  \\ fs [has_compiled_def]
  \\ every_case_tac \\ fs []
  \\ res_tac \\ fs [next_def] \\ rveq
  \\ Cases_on `cs'` \\ fs [code_subset_def,install_def]
  \\ rw [] \\ fs []);

val has_compiled_lemma = prove(
  ``state_rel s1 t1 cs2 t0 frame ∧
    has_compiled p cs = INL x /\ code_subset cs cs2 ==>
    ?cs0 p1 l1 i1 cs' cs1.
      compile x 1 1 cs' p = (p1,l1,i1,cs1) /\ code_subset cs1 cs2 /\
      lookup x t1.code = SOME (1,Seq p1 (Return 0 0))``,
  Cases_on `cs`
  \\ Cases_on `cs2`
  \\ fs [state_rel_def,code_rel_def,has_compiled_def]
  \\ rw []
  \\ rename1 `code_subset (q1,r1) (q2,r2)`
  \\ Cases_on `ALOOKUP r1 p` \\ fs []
  \\ every_case_tac \\ fs [] \\ rveq
  \\ fs [code_subset_def]
  \\ res_tac \\ res_tac
  \\ asm_exists_tac \\ fs []);

val state_rel_IN_FDOM = prove(
  ``state_rel s1 t1 cs2 t0 frame /\ r ∈ FDOM s1.regs ==>
    Temp (n2w r) ∈ FDOM t1.store /\
    t1.store ' (Temp (n2w r)) = Word (s1.regs ' r)``,
  fs [state_rel_def] \\ rw [] \\ fs [FLOOKUP_DEF]);

val compile_exp_thm = prove(
  ``state_rel s1 t1 cs2 t0 frame /\ eval_exp_pre s1 x /\ good_dimindex (:α) ==>
    word_exp t1 (compile_exp x) = SOME (Word (eval_exp s1 (x:'a wordLang$exp)))``,
  completeInduct_on `wordLang$exp_size (K 0) x`
  \\ rw [] \\ fs [PULL_FORALL]
  \\ Cases_on `x`
  \\ fs [word_exp_def,eval_exp_def,eval_exp_pre_def,compile_exp_def]
  THEN1 (imp_res_tac state_rel_IN_FDOM \\ fs [FLOOKUP_DEF])
  THEN1
   (Cases_on `l` \\ fs [eval_exp_pre_def]
    \\ Cases_on `t` \\ fs [eval_exp_pre_def]
    \\ Cases_on `t'` \\ fs [eval_exp_pre_def]
    \\ fs [word_exp_def,eval_exp_def,eval_exp_pre_def,compile_exp_def]
    \\ fs [exp_size_def]
    \\ qabbrev_tac `l = binop_size b + (exp_size (K 0) h + (exp_size (K 0) h' + 3))`
    \\ `exp_size (K 0) h < l /\ exp_size (K 0) h' < l` by
         (unabbrev_all_tac \\ decide_tac)
    \\ fs [the_words_def]
    \\ Cases_on `b` \\ fs [word_op_def,eval_exp_def])
  \\ Cases_on `n`
  \\ fs [word_exp_def,eval_exp_def,eval_exp_pre_def,compile_exp_def] \\ rveq
  \\ fs [compile_exp_def]
  \\ `exp_size (K 0) e < exp_size (K 0) (Shift s e (Nat 1))` by
       (fs [exp_size_def] \\ decide_tac)
  \\ res_tac \\ fs [num_exp_def]
  \\ Cases_on `s`
  \\ fs [word_sh_def,eval_exp_def]
  \\ fs [good_dimindex_def]);

val evaluate_SeqTemp = prove(
  ``evaluate (SeqTemp i r p,t) =
    if Temp (n2w r) IN FDOM t.store then
       evaluate (p,set_var i (t.store ' (Temp (n2w r))) t)
    else evaluate (SeqTemp i r p,t)``,
  rw [] \\ fs [SeqTemp_def,evaluate_def,word_exp_def,FLOOKUP_DEF]);

val evaluate_SeqTempImm = prove(
  ``evaluate (SeqTempImm i ri p,t) =
    if !r. ri = Reg r ==> Temp (n2w r) IN FDOM t.store then
       evaluate (p,set_var i (case ri of Imm w => Word w
                              | Reg r => t.store ' (Temp (n2w r))) t)
    else evaluate (SeqTempImm i ri p,t)``,
  Cases_on `ri` \\ fs [SeqTempImm_def]
  \\ once_rewrite_tac [evaluate_SeqTemp]
  \\ fs [] \\ rw [] \\ fs []
  \\ fs [SeqTemp_def,evaluate_def,word_exp_def,FLOOKUP_DEF]);

val evaluate_SeqTempImmNot = prove(
  ``evaluate (SeqTempImmNot i ri p,t) =
    if !r. ri = Reg r ==> Temp (n2w r) IN FDOM t.store /\
                          ?w. t.store ' (Temp (n2w r)) = Word w then
       evaluate (p,set_var i (case ri of Imm w => Word (~w)
                              | Reg r => case t.store ' (Temp (n2w r)) of
                                         | Word w => Word (~w)) t)
    else evaluate (SeqTempImmNot i ri p,t)``,
  Cases_on `ri` \\ fs [SeqTempImmNot_def]
  \\ fs [SeqTemp_def,evaluate_def,word_exp_def,FLOOKUP_DEF]
  \\ rw [] \\ fs [set_var_def,the_words_def,word_op_def]
  \\ fs [insert_shadow]);

val LESS_LENGTH_IMP_APPEND = prove(
  ``!xs n. n < LENGTH xs ==>
           ?ys z zs. xs = ys ++ z::zs /\ LENGTH ys = n``,
  Induct \\ fs [] \\ Cases_on `n` \\ fs [LENGTH_NIL]
  \\ rw [] \\ res_tac \\ fs [] \\ qexists_tac `h::ys` \\ fs []);

val word_list_APPEND = Q.store_thm("word_list_APPEND",
  `!xs ys a. word_list a (xs ++ ys) =
              word_list a xs * word_list (a + n2w (LENGTH xs) * bytes_in_word) ys`,
  Induct \\ full_simp_tac(srw_ss())[word_list_def,SEP_CLAUSES,STAR_ASSOC,ADD1,
                GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]);

val shift_eq_bytes_in_word = prove(
  ``good_dimindex (:'a) ==>
    (w << shift (:'a) = w * bytes_in_word:'a word)``,
  fs [shift_def,good_dimindex_def] \\ rw []
  \\ fs [WORD_MUL_LSL,bytes_in_word_def]);

val b2w_if = prove(
  ``b2w b = if b then 1w else 0w``,
  Cases_on `b` \\ EVAL_TAC);

val b2n_if = prove(
  ``b2n b = if ~b then 0 else 1``,
  Cases_on `b` \\ EVAL_TAC);

val compile_thm = store_thm("compile_thm",
  ``!s1 prog s2.
      Eval s1 prog s2 ==>
      !n l i cs p1 l1 i1 cs1 cs2 t1 (ret_val:'a word_loc) p9.
        compile n l i cs prog = (p1,l1,i1,cs1) /\
        state_rel s1 t1 cs2 t0 frame /\ 0 < i /\
        syntax_ok prog /\ code_subset cs1 cs2 /\
        (!body. prog = LoopBody body ==>
                p9 = Return 0 0 /\
                lookup n t1.code = SOME (1,Seq p1 (Return 0 0))) /\
        get_var 0 t1 = SOME ret_val /\ good_dimindex (:'a) ==>
        ?t2 res.
          (evaluate (Seq p1 p9,t1) = res) /\
          case s2 of
          | INR s => res = evaluate (p9,t2) /\
                     0 < i1 /\
                     t2.stack = t1.stack /\
                     get_var 0 t2 = SOME ret_val /\
                     state_rel s t2 cs2 t0 frame
          | INL s => res = evaluate (Call NONE (SOME n) [0] NONE,t2) /\
                     0 < i1 /\
                     t2.stack = t1.stack /\
                     get_var 0 t2 = SOME ret_val /\
                     state_rel s t2 cs2 t0 frame``,
  ho_match_mp_tac eval_ind \\ rpt strip_tac
  THEN1 (* Skip *)
    (fs [compile_def] \\ rveq \\ fs [evaluate_def]
     \\ qexists_tac `t1` \\ fs [])
  THEN1 (* Continue *)
    (fs [compile_def] \\ rveq \\ fs [evaluate_def]
     \\ qexists_tac `t1` \\ fs []
     \\ every_case_tac \\ fs [])
  THEN1 (* Delete *)
    (fs [compile_def] \\ rveq \\ fs [evaluate_def]
     \\ qexists_tac `t1` \\ fs [state_rel_delete_vars])
  THEN1 (* Assign *)
    (fs [compile_def] \\ rveq
     \\ fs [evaluate_def]
     \\ drule compile_exp_thm \\ fs [] \\ strip_tac
     \\ fs [word_exp_def,set_var_def,lookup_insert]
     \\ qpat_abbrev_tac `s6 = set_store _ _ _`
     \\ qexists_tac `s6` \\ fs []
     \\ unabbrev_all_tac \\ fs [set_store_def,get_var_def,lookup_insert]
     \\ fs [state_rel_def,reg_write_def,FLOOKUP_UPDATE]
     \\ fs [syntax_ok_def,syntax_ok_aux_def]
     \\ fs [TempIn1_def,TempIn2_def,TempOut_def]
     \\ strip_tac \\ Cases_on `n = a` \\ fs []
     \\ rpt strip_tac \\ res_tac  \\ fs [])
  THEN1 (* Seq *)
    (fs [compile_def]
     \\ rpt (pairarg_tac \\ fs []) \\ rveq
     \\ qpat_x_assum `!x. _` mp_tac
     \\ first_x_assum drule
     \\ `code_subset cs' cs2` by metis_tac [code_subset_trans,compile_IMP_code_subset]
     \\ disch_then drule \\ fs []
     \\ `syntax_ok prog /\ !b. prog <> LoopBody b` by
          (Cases_on `prog` \\ fs [syntax_ok_def,syntax_ok_aux_def] \\ NO_TAC)
     \\ `syntax_ok prog' /\ !b. prog' <> LoopBody b` by
          (Cases_on `prog'` \\ fs [syntax_ok_def,syntax_ok_aux_def] \\ NO_TAC)
     \\ fs []
     \\ disch_then (qspec_then `Seq p2 p9` mp_tac)
     \\ strip_tac \\ fs [evaluate_Seq_Seq]
     \\ disch_then drule \\ fs []
     \\ disch_then drule \\ fs [])
  THEN1 (* If *)
    (fs [compile_def]
     \\ `syntax_ok p1 /\ !b. p1 <> LoopBody b` by
          (Cases_on `p1` \\ fs [syntax_ok_def,syntax_ok_aux_def] \\ NO_TAC)
     \\ `syntax_ok p2 /\ !b. p2 <> LoopBody b` by
          (Cases_on `p2` \\ fs [syntax_ok_def,syntax_ok_aux_def] \\ NO_TAC)
     \\ Cases_on `ri` \\ fs [eval_ri_pre_def,eval_exp_pre_def]
     \\ rpt (pairarg_tac \\ fs [] \\ rveq)
     \\ simp [evaluate_def]
     \\ once_rewrite_tac [evaluate_SeqTemp] \\ fs []
     \\ once_rewrite_tac [evaluate_SeqTemp] \\ fs []
     \\ fs [set_var_def]
     \\ drule (GEN_ALL state_rel_IN_FDOM) \\ strip_tac \\ fs []
     \\ fs [evaluate_def,get_var_def,lookup_insert,get_var_imm_def]
     \\ IF_CASES_TAC \\ fs [eval_ri_def,eval_exp_def]
     \\ Q.MATCH_GOALSUB_ABBREV_TAC `wordSem$evaluate (_,t5)`
     \\ qpat_assum `!v1 v2. _` drule
     \\ `state_rel s1 t5 cs2 t0 frame` by
          (unabbrev_all_tac \\ fs [state_rel_def] \\ NO_TAC)
     \\ disch_then drule
     \\ imp_res_tac compile_IMP_code_subset
     \\ imp_res_tac code_subset_trans
     \\ `lookup 0 t5.locals = SOME ret_val` by
          (unabbrev_all_tac \\ fs [lookup_insert] \\ NO_TAC)
     \\ fs []
     \\ disch_then (qspec_then `p9` mp_tac)
     \\ strip_tac \\ fs []
     \\ Cases_on `s2 ` \\ fs []
     \\ qexists_tac `t2` \\ fs []
     \\ unabbrev_all_tac \\ fs [])
  THEN1 (* Load *)
   (fs [compile_def] \\ rveq \\ fs [FLOOKUP_DEF]
    \\ imp_res_tac state_rel_IN_FDOM
    \\ qpat_assum `state_rel s1 t1 cs2 t0 frame`
         (fn th => assume_tac (REWRITE_RULE [state_rel_def] th))
    \\ fs [SeqIndex_def,evaluate_def,array_rel_def]
    \\ Cases_on `a`
    \\ fs [word_exp_def,FLOOKUP_DEF,word_sh_def,num_exp_def]
    \\ `shift (:α) < dimindex (:α)` by
          (fs [good_dimindex_def,shift_def] \\ NO_TAC)
    \\ fs [the_words_def,word_op_def,set_var_def,lookup_insert,
           mem_load_def]
    \\ imp_res_tac LESS_LENGTH_IMP_APPEND
    \\ fs [word_list_def,word_list_APPEND,shift_eq_bytes_in_word]
    \\ SEP_R_TAC \\ fs []
    \\ pop_assum (fn th => fs [GSYM th])
    \\ full_simp_tac std_ss [EL_LENGTH_APPEND,NULL_DEF,GSYM APPEND_ASSOC,APPEND,HD]
    \\ qpat_abbrev_tac `s4 = set_store _ _ _`
    \\ qexists_tac `s4` \\ fs []
    \\ unabbrev_all_tac \\ fs [set_store_def,get_var_def,lookup_insert]
    \\ fs [state_rel_def,reg_write_def,FLOOKUP_UPDATE]
    \\ res_tac \\ fs [TempIn1_def,TempIn2_def,TempOut_def]
    \\ fs [syntax_ok_def,syntax_ok_aux_def]
    \\ strip_tac \\ Cases_on `r = a` \\ fs []
    \\ rpt strip_tac \\ fs [FLOOKUP_DEF]
    \\ `a < max_var_name` by fs [] \\ fs [])
  THEN1 (* Store *)
   (fs [compile_def] \\ rveq \\ fs [FLOOKUP_DEF]
    \\ imp_res_tac state_rel_IN_FDOM
    \\ qpat_assum `state_rel s1 t1 cs2 t0 frame`
         (fn th => assume_tac (REWRITE_RULE [state_rel_def] th))
    \\ fs [SeqIndex_def,evaluate_def,array_rel_def]
    \\ once_rewrite_tac [evaluate_SeqTemp] \\ fs [evaluate_def]
    \\ fs [word_exp_def,FLOOKUP_DEF,word_sh_def,num_exp_def,set_var_def]
    \\ `shift (:α) < dimindex (:α)` by
          (fs [good_dimindex_def,shift_def] \\ NO_TAC)
    \\ fs [the_words_def,word_op_def,set_var_def,lookup_insert,get_var_def,
           mem_store_def]
    \\ imp_res_tac LESS_LENGTH_IMP_APPEND
    \\ fs [word_list_def,word_list_APPEND,shift_eq_bytes_in_word,SEP_CLAUSES]
    \\ SEP_R_TAC \\ fs []
    \\ pop_assum (fn th => fs [GSYM th] THEN assume_tac th)
    \\ fs [lupdate_append2]
    \\ Q.MATCH_GOALSUB_ABBREV_TAC `(p9,t5)`
    \\ qexists_tac `t5` \\ fs []
    \\ unabbrev_all_tac \\ fs [get_var_def,lookup_insert]
    \\ fs [state_rel_def,array_write_def,FLOOKUP_UPDATE]
    \\ simp [array_rel_def]
    \\ fs [APPLY_UPDATE_THM,word_list_APPEND,word_list_def]
    \\ fs [SEP_CLAUSES]
    \\ fs [FLOOKUP_DEF]
    \\ qexists_tac `rest1`
    \\ qexists_tac `rest2`
    \\ rpt strip_tac
    \\ qabbrev_tac `m = t1.memory`
    \\ qabbrev_tac `dm = t1.mdomain`
    \\ SEP_WRITE_TAC)
  THEN1 (* Swap *)
   (fs [compile_def] \\ rveq
    \\ fs [evaluate_def,word_exp_def,state_rel_def,array_rel_def,array_write_def,
           TempIn1_def,TempIn2_def,TempOut_def,set_var_def,set_store_def,
           FLOOKUP_UPDATE,APPLY_UPDATE_THM,get_var_def,lookup_insert]
    \\ Q.MATCH_GOALSUB_ABBREV_TAC `(p9,t5)`
    \\ qexists_tac `t5` \\ unabbrev_all_tac \\ fs []
    \\ fs [evaluate_def,word_exp_def,state_rel_def,array_rel_def,array_write_def,
           TempIn1_def,TempIn2_def,TempOut_def,set_var_def,set_store_def,
           FLOOKUP_UPDATE,APPLY_UPDATE_THM,get_var_def,lookup_insert]
    \\ rpt strip_tac
    \\ res_tac \\ fs []
    \\ rpt (asm_exists_tac \\ fs []))
  THEN1 (* Add *)
   (fs [compile_def] \\ rveq
    \\ fs [evaluate_def]
    \\ imp_res_tac state_rel_IN_FDOM
    \\ once_rewrite_tac [evaluate_SeqTempImm]
    \\ reverse IF_CASES_TAC THEN1
     (fs [] \\ rveq \\ fs []
      \\ fs [eval_ri_pre_def,eval_exp_pre_def]
      \\ imp_res_tac state_rel_IN_FDOM)
    \\ fs [set_var_def]
    \\ once_rewrite_tac [evaluate_SeqTempImm]
    \\ reverse IF_CASES_TAC THEN1
     (fs [] \\ rveq \\ fs []
      \\ fs [eval_ri_pre_def,eval_exp_pre_def]
      \\ imp_res_tac state_rel_IN_FDOM)
    \\ fs [set_var_def]
    \\ once_rewrite_tac [evaluate_SeqTemp] \\ fs [set_var_def]
    \\ fs [evaluate_def,inst_def,get_vars_def,get_var_def,lookup_insert,
           set_var_def,word_exp_def,set_store_def]
    \\ Cases_on `n4` \\ fs []
    \\ Cases_on `n5` \\ fs []
    \\ fs [eval_ri_pre_def,eval_exp_pre_def]
    \\ imp_res_tac state_rel_IN_FDOM
    \\ fs [lookup_insert]
    \\ Q.MATCH_GOALSUB_ABBREV_TAC `(p9,t5)`
    \\ qexists_tac `t5` \\ unabbrev_all_tac \\ fs []
    \\ fs [lookup_insert]
    \\ fs [evaluate_def,word_exp_def,state_rel_def,reg_write_def,
           TempIn1_def,TempIn2_def,TempOut_def,set_var_def,set_store_def,
           FLOOKUP_UPDATE,APPLY_UPDATE_THM,get_var_def,lookup_insert]
    \\ fs [FLOOKUP_DEF]
    \\ res_tac \\ fs [syntax_ok_def,syntax_ok_aux_def]
    \\ strip_tac
    \\ fs [single_add_word_def,multiwordTheory.single_add_def] \\ rveq
    \\ fs [b2w_if,eval_ri_def,eval_exp_def,b2n_if]
    \\ fs [GSYM word_add_n2w]
    \\ rpt (IF_CASES_TAC \\ fs [])
    \\ rpt strip_tac \\ res_tac \\ fs [])
  THEN1 (* Sub *)
   (fs [compile_def] \\ rveq
    \\ fs [evaluate_def]
    \\ imp_res_tac state_rel_IN_FDOM
    \\ once_rewrite_tac [evaluate_SeqTempImm]
    \\ reverse IF_CASES_TAC THEN1
     (fs [] \\ rveq \\ fs []
      \\ fs [eval_ri_pre_def,eval_exp_pre_def]
      \\ imp_res_tac state_rel_IN_FDOM)
    \\ fs [set_var_def]
    \\ once_rewrite_tac [evaluate_SeqTempImmNot]
    \\ reverse IF_CASES_TAC THEN1
     (`F` by all_tac \\ pop_assum mp_tac \\ fs []
      \\ Cases_on `n4` \\ fs []
      \\ fs [eval_ri_pre_def,eval_exp_pre_def]
      \\ imp_res_tac state_rel_IN_FDOM \\ fs [])
    \\ fs [set_var_def]
    \\ once_rewrite_tac [evaluate_SeqTemp] \\ fs [set_var_def]
    \\ fs [evaluate_def,inst_def,get_vars_def,get_var_def,lookup_insert,
           set_var_def,word_exp_def,set_store_def]
    \\ Cases_on `n4` \\ fs []
    \\ Cases_on `n5` \\ fs []
    \\ fs [eval_ri_pre_def,eval_exp_pre_def]
    \\ imp_res_tac state_rel_IN_FDOM
    \\ fs [lookup_insert]
    \\ Q.MATCH_GOALSUB_ABBREV_TAC `(p9,t5)`
    \\ qexists_tac `t5` \\ unabbrev_all_tac \\ fs []
    \\ fs [lookup_insert]
    \\ fs [evaluate_def,word_exp_def,state_rel_def,reg_write_def,
           TempIn1_def,TempIn2_def,TempOut_def,set_var_def,set_store_def,
           FLOOKUP_UPDATE,APPLY_UPDATE_THM,get_var_def,lookup_insert]
    \\ fs [FLOOKUP_DEF]
    \\ res_tac \\ fs [syntax_ok_def,syntax_ok_aux_def]
    \\ strip_tac
    \\ fs [single_sub_word_def,multiwordTheory.single_add_def,
           multiwordTheory.single_sub_def] \\ rveq
    \\ fs [b2w_if,eval_ri_def,eval_exp_def,b2n_if]
    \\ fs [GSYM word_add_n2w]
    \\ rpt (IF_CASES_TAC \\ fs [])
    \\ rpt strip_tac \\ res_tac \\ fs [])
  THEN1 (* Mul *)
   (fs [compile_def] \\ rveq
    \\ fs [evaluate_def]
    \\ fs [FLOOKUP_DEF]
    \\ imp_res_tac state_rel_IN_FDOM
    \\ once_rewrite_tac [evaluate_SeqTemp] \\ fs [set_var_def]
    \\ once_rewrite_tac [evaluate_SeqTemp] \\ fs [set_var_def]
    \\ fs [evaluate_def,inst_def,get_vars_def,get_var_def,lookup_insert,
           set_var_def,word_exp_def,set_store_def]
    \\ Q.MATCH_GOALSUB_ABBREV_TAC `(p9,t5)`
    \\ qexists_tac `t5` \\ unabbrev_all_tac \\ fs []
    \\ fs [lookup_insert]
    \\ fs [evaluate_def,word_exp_def,state_rel_def,reg_write_def,
           TempIn1_def,TempIn2_def,TempOut_def,set_var_def,set_store_def,
           FLOOKUP_UPDATE,APPLY_UPDATE_THM,get_var_def,lookup_insert]
    \\ fs [FLOOKUP_DEF]
    \\ res_tac \\ fs [syntax_ok_def,syntax_ok_aux_def]
    \\ strip_tac
    \\ Cases_on `a = n1` \\ fs []
    THEN1 (fs [multiwordTheory.single_mul_def,GSYM word_mul_n2w])
    \\ Cases_on `a = n2` \\ fs []
    THEN1 (fs [multiwordTheory.single_mul_def,GSYM word_mul_n2w])
    \\ strip_tac \\ res_tac \\ fs [])
  THEN1 (* Div *)
   (fs [compile_def] \\ rveq
    \\ fs [evaluate_def]
    \\ fs [FLOOKUP_DEF]
    \\ imp_res_tac state_rel_IN_FDOM
    \\ once_rewrite_tac [evaluate_SeqTemp] \\ fs [set_var_def]
    \\ once_rewrite_tac [evaluate_SeqTemp] \\ fs [set_var_def]
    \\ once_rewrite_tac [evaluate_SeqTemp] \\ fs [set_var_def]
    \\ fs [evaluate_def,inst_def,get_vars_def,get_var_def,lookup_insert,
           set_var_def,word_exp_def,set_store_def,single_div_pre_def]
    \\ Q.MATCH_GOALSUB_ABBREV_TAC `(p9,t5)`
    \\ qexists_tac `t5` \\ unabbrev_all_tac \\ fs []
    \\ fs [lookup_insert]
    \\ fs [evaluate_def,word_exp_def,state_rel_def,reg_write_def,
           TempIn1_def,TempIn2_def,TempOut_def,set_var_def,set_store_def,
           FLOOKUP_UPDATE,APPLY_UPDATE_THM,get_var_def,lookup_insert]
    \\ fs [FLOOKUP_DEF]
    \\ res_tac \\ fs [syntax_ok_def,syntax_ok_aux_def]
    \\ strip_tac
    \\ Cases_on `a = n1` \\ fs []
    THEN1 (fs [multiwordTheory.single_div_def,GSYM word_mul_n2w])
    \\ Cases_on `a = n2` \\ fs []
    THEN1 (fs [multiwordTheory.single_div_def,GSYM word_mul_n2w])
    \\ strip_tac \\ res_tac \\ fs [])
  THEN1 (* Loop *)
   (fs [compile_def]
    \\ fs [syntax_ok_def,syntax_ok_aux_def]
    \\ Cases_on `has_compiled p cs` \\ fs [] \\ rveq
    THEN1
     (simp [Once evaluate_def] \\ simp [Once evaluate_def]
      \\ `t1.clock <> 0` by fs [state_rel_def]
      \\ simp [get_vars_def,bad_dest_args_def,add_ret_loc_def,find_code_def]
      \\ `wordSem$cut_env (LS ()) t1.locals = SOME (insert 0 ret_val LN)` by
       (fs [wordSemTheory.cut_env_def,domain_lookup,get_var_def]
        \\ fs [spt_eq_thm,wf_insert,wf_def,lookup_insert,
               lookup_def,lookup_inter_alt] \\ NO_TAC) \\ fs []
      \\ drule (GEN_ALL has_compiled_lemma)
      \\ disch_then drule
      \\ fs [] \\ strip_tac \\ fs []
      \\ Q.MATCH_GOALSUB_ABBREV_TAC `(Seq p1 (Return 0 0),t5)`
      \\ first_x_assum drule
      \\ disch_then (qspecl_then [`cs2`,`t5`] mp_tac)
      \\ `get_var 0 t5 = SOME (Loc n l)` by (unabbrev_all_tac \\ EVAL_TAC \\ NO_TAC)
      \\ fs []
      \\ impl_tac THEN1
       (unabbrev_all_tac
        \\ fs [call_env_def,push_env_def,env_to_list_insert_0_LN,
               wordSemTheory.dec_clock_def]
        \\ match_mp_tac state_rel_delete_vars
        \\ fs [dec_clock_def,wordSemTheory.dec_clock_def]
        \\ fs [state_rel_def])
      \\ strip_tac \\ fs []
      \\ fs [evaluate_def]
      \\ unabbrev_all_tac
      \\ fs [pop_env_def,call_env_def,push_env_def]
      \\ fs [env_to_list_insert_0_LN,EVAL ``domain (fromAList [(0,ret_val)])``]
      \\ fs [set_var_def,fromAList_def,wordSemTheory.dec_clock_def]
      \\ Q.MATCH_GOALSUB_ABBREV_TAC `(p9,t8)`
      \\ qexists_tac `t8` \\ fs []
      \\ unabbrev_all_tac \\ fs [get_var_def,lookup_insert]
      \\ fs [state_rel_def])
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ qabbrev_tac `cs1 = install (p,y,Seq new_code (Return 0 0)) cs'`
    \\ `has_compiled p cs1 = INL y` by
     (fs [has_compiled_def,Abbr`cs1`]
      \\ Cases_on `cs'` \\ Cases_on `cs` \\ fs []
      \\ fs [install_def,has_compiled_def])
    \\ simp [Once evaluate_def] \\ simp [Once evaluate_def]
    \\ `t1.clock <> 0` by fs [state_rel_def]
    \\ simp [get_vars_def,bad_dest_args_def,add_ret_loc_def,find_code_def]
    \\ `wordSem$cut_env (LS ()) t1.locals = SOME (insert 0 ret_val LN)` by
     (fs [wordSemTheory.cut_env_def,domain_lookup,get_var_def]
      \\ fs [spt_eq_thm,wf_insert,wf_def,lookup_insert,
             lookup_def,lookup_inter_alt] \\ NO_TAC) \\ fs []
    \\ drule (GEN_ALL has_compiled_lemma)
    \\ disch_then drule
    \\ fs [] \\ strip_tac \\ fs []
    \\ Q.MATCH_GOALSUB_ABBREV_TAC `(Seq p1 (Return 0 0),t5)`
    \\ first_x_assum drule
    \\ disch_then (qspecl_then [`cs2`,`t5`] mp_tac)
    \\ `get_var 0 t5 = SOME (Loc n l)` by (unabbrev_all_tac \\ EVAL_TAC \\ NO_TAC)
    \\ fs []
    \\ impl_tac THEN1
     (unabbrev_all_tac
      \\ fs [call_env_def,push_env_def,env_to_list_insert_0_LN,
             wordSemTheory.dec_clock_def]
      \\ match_mp_tac state_rel_delete_vars
      \\ fs [dec_clock_def,wordSemTheory.dec_clock_def]
      \\ fs [state_rel_def])
    \\ strip_tac \\ fs []
    \\ fs [evaluate_def]
    \\ unabbrev_all_tac
    \\ fs [pop_env_def,call_env_def,push_env_def]
    \\ fs [env_to_list_insert_0_LN,EVAL ``domain (fromAList [(0,ret_val)])``]
    \\ fs [set_var_def,fromAList_def,wordSemTheory.dec_clock_def]
    \\ Q.MATCH_GOALSUB_ABBREV_TAC `(p9,t8)`
    \\ qexists_tac `t8` \\ fs []
    \\ unabbrev_all_tac \\ fs [get_var_def,lookup_insert]
    \\ fs [state_rel_def])
  THEN1 (* LoopBody ret *)
   (fs [syntax_ok_def,compile_def]
    \\ `syntax_ok prog /\ !r. prog <> LoopBody r` by
     (fs [syntax_ok_def] \\ Cases_on `prog`
      \\ fs [syntax_ok_aux_def,syntax_ok_def]) \\ fs []
    \\ first_x_assum match_mp_tac
    \\ asm_exists_tac \\ fs [])
  THEN1 (* LoopBody cont *)
   (fs [compile_def] \\ rveq
    \\ `syntax_ok prog /\ !r. prog <> LoopBody r` by
     (fs [syntax_ok_def] \\ Cases_on `prog`
      \\ fs [syntax_ok_aux_def,syntax_ok_def]) \\ fs []
    \\ qpat_x_assum `!v w._` mp_tac
    \\ first_x_assum drule
    \\ disch_then drule \\ fs []
    \\ disch_then (qspec_then `Return 0 0` strip_assume_tac) \\ fs []
    \\ disch_then drule \\ fs []
    \\ `state_rel (dec_clock s2) (call_env [ret_val] (dec_clock t2)) cs2 t0 frame` by
      (fs [state_rel_def,call_env_def,wordSemTheory.dec_clock_def,dec_clock_def]
       \\ NO_TAC)
    \\ disch_then drule
    \\ `get_var 0 (call_env [ret_val] (dec_clock t2)) = SOME ret_val` by
      (fs [get_var_def,call_env_def,dec_clock_def,state_rel_def] \\ EVAL_TAC)
    \\ fs []
    \\ impl_tac THEN1 fs [call_env_def,dec_clock_def,state_rel_def]
    \\ strip_tac \\ fs []
    \\ simp [Once evaluate_def,get_vars_def]
    \\ `t2.clock <> 0` by fs [state_rel_def] \\ fs []
    \\ fs [bad_dest_args_def,add_ret_loc_def,find_code_def]
    \\ `t2.code = t1.code` by fs [state_rel_def]
    \\ fs [] \\ qexists_tac `t2'` \\ fs []
    \\ fs [call_env_def,wordSemTheory.dec_clock_def]
    \\ fs [evaluate_def]
    \\ every_case_tac \\ fs []));


(* correctenss judgement *)

val all_corrs = ref (tl [TRUTH]);

val Corr_def = Define `
  Corr prog (s:'a state) s1 p <=>
    (p ==> Eval s prog s1)`;

val Corr_Skip = prove(
  ``Corr Skip s (INR s) T``,
  fs [Corr_def,eval_cases]);

val Corr_Seq = prove(
  ``Corr p2 s1 s2 q2 ==>
    Corr p1 s (INR s1) q1 ==>
    Corr (Seq p1 p2) s s2 (q1 /\ q2)``,
  fs [Corr_def,eval_cases] \\ rw [] \\ fs []
  \\ asm_exists_tac \\ fs []);

val Corr_Seq_alt = prove(
  ``(b ==> Corr p2 s1 s2 q2) ==>
    Corr p1 s (INR s1) q1 ==>
    b ==> Corr (Seq p1 p2) s s2 (q1 /\ q2)``,
  fs [Corr_def,eval_cases] \\ rw [] \\ fs []
  \\ asm_exists_tac \\ fs []);

val Corr_Continue = prove(
  ``Corr Continue s (INL s) T``,
  fs [Corr_def,eval_cases]);

val Corr_Assign = prove(
  ``Corr (Assign n x) s
      (INR (reg_write n (SOME (eval_exp s x)) s))
      (eval_exp_pre s x)``,
  fs [Corr_def,eval_cases]);

val Corr_Delete = prove(
  ``Corr (Delete vs) s (INR (delete_vars vs s)) T``,
  fs [Corr_def,eval_cases,FLOOKUP_DEF]);

val Corr_Load = prove(
  ``Corr (Load r i a) s
        (INR (reg_write r (SOME (EL (w2n (s.regs ' i)) (s.arrays a))) s))
        (i IN FDOM s.regs /\ w2n (s.regs ' i) < LENGTH (s.arrays a))``,
  fs [Corr_def,eval_cases,FLOOKUP_DEF]);

val Corr_Store = prove(
  ``Corr (Store r i) s
        (INR (array_write Out (LUPDATE (s.regs ' r) (w2n (s.regs ' i))
                    (s.arrays Out)) s))
        (r IN FDOM s.regs /\ i IN FDOM s.regs /\
         w2n (s.regs ' i) < LENGTH (s.arrays Out))``,
  fs [Corr_def,eval_cases,FLOOKUP_DEF]);

val Corr_Swap = prove(
  ``Corr Swap s
      (INR (array_write In1 (s.arrays In2) (array_write In2 (s.arrays In1) s))) T``,
  fs [Corr_def,eval_cases,FLOOKUP_DEF]
  \\ fs [fetch "-" "state_component_equality"]
  \\ rw [] \\ qexists_tac `s` \\ fs []);

val Corr_Add = prove(
  ``Corr (Add n1 n2 n3 ri1 ri2) s
     (INR (reg_write n1
            (SOME (FST (single_add_word (s.regs ' n3) (eval_ri s ri1) (eval_ri s ri2))))
          (reg_write n2
            (SOME (SND (single_add_word (s.regs ' n3) (eval_ri s ri1) (eval_ri s ri2)))) s)))
     (n3 ∈ FDOM s.regs ∧ eval_ri_pre s ri1 ∧ eval_ri_pre s ri2 /\
      (eval_ri s ri2 ≠ 0w ==> eval_ri s ri2 = 1w) /\ n1 <> n2)``,
  fs [Corr_def,eval_cases]
  \\ fs [fetch "-" "state_component_equality"] \\ rw []
  \\ fs [single_add_word_def,multiwordTheory.single_add_def]);

val Corr_Sub = prove(
  ``Corr (Sub n1 n2 n3 ri1 ri2) s
     (INR (reg_write n1
            (SOME (FST (single_sub_word (s.regs ' n3) (eval_ri s ri1) (eval_ri s ri2))))
          (reg_write n2
            (SOME (SND (single_sub_word (s.regs ' n3) (eval_ri s ri1) (eval_ri s ri2)))) s)))
     (n3 ∈ FDOM s.regs ∧ eval_ri_pre s ri1 ∧ eval_ri_pre s ri2 /\
      (eval_ri s ri2 ≠ 0w ==> eval_ri s ri2 = 1w) /\ n1 <> n2)``,
  fs [Corr_def,eval_cases]
  \\ fs [fetch "-" "state_component_equality"] \\ rw []
  \\ fs [single_sub_word_def,multiwordTheory.single_add_def,
         multiwordTheory.single_sub_def]);

val Corr_Mul = prove(
  ``Corr (Mul n1 n2 n3 n4) s
     (INR (reg_write n1 (SOME (FST (single_mul (s.regs ' n3) (s.regs ' n4) 0w)))
          (reg_write n2 (SOME (SND (single_mul (s.regs ' n3) (s.regs ' n4) 0w))) s)))
     (n3 ∈ FDOM s.regs ∧ n4 ∈ FDOM s.regs /\ n1 <> n2)``,
  fs [Corr_def,eval_cases]
  \\ fs [fetch "-" "state_component_equality"] \\ rw []);

val Corr_Div = prove(
  ``Corr (Div n1 n2 n3 n4 n5) s
     (INR (reg_write n1
             (SOME (FST (single_div (s.regs ' n3) (s.regs ' n4) (s.regs ' n5))))
          (reg_write n2
             (SOME (SND (single_div (s.regs ' n3) (s.regs ' n4) (s.regs ' n5)))) s)))
     (n3 ∈ FDOM s.regs ∧ n4 ∈ FDOM s.regs ∧ n5 ∈ FDOM s.regs /\ n1 <> n2 /\
      single_div_pre (s.regs ' n3) (s.regs ' n4) (s.regs ' n5))``,
  fs [Corr_def,eval_cases]
  \\ fs [fetch "-" "state_component_equality"] \\ rw []);

val Corr_If = prove(
  ``Corr p1 s f1 q1 /\ Corr p2 s f2 q2 ==>
    Corr (If c r ri p1 p2) s
      (if word_cmp c (eval_exp s (Var r)) (eval_ri s ri) then f1 else f2)
      (r IN FDOM s.regs /\ eval_ri_pre s ri /\
       if word_cmp c (eval_exp s (Var r)) (eval_ri s ri) then q1 else q2)``,
  fs [Corr_def,eval_cases] \\ rw [] \\ fs []
  \\ asm_exists_tac \\ fs [] \\ rw [] \\ fs []);

val loop_app_def = Define `
  loop_app f g x =
    case f x of
    | INL s => (INL (dec_clock s), g x /\ s.clock <> 0)
    | INR s => (INR s, g x)`;

val Corr_LoopBody = prove(
  ``(!s. Corr p s (f s) (q s)) ==>
    !s. Corr (LoopBody p) s (INR (SHORT_TAILREC (loop_app f q) s))
                                 (SHORT_TAILREC_PRE (loop_app f q) s)``,
  fs [Corr_def,SHORT_TAILREC_PRE_def,SHORT_TAILREC_def] \\ strip_tac
  \\ ho_match_mp_tac TAILREC_PRE_INDUCT \\ reverse (rw [])
  \\ fs [loop_app_def]
  \\ once_rewrite_tac [eval_cases] THENL [disj1_tac,disj2_tac]
  \\ once_rewrite_tac [TAILREC_THM]
  \\ fs [] \\ res_tac \\ fs [loop_app_def]
  \\ Cases_on `f s` \\ fs []
  \\ qpat_x_assum `!x. _` imp_res_tac \\ rfs []
  \\ asm_exists_tac \\ fs []);

val tick_before_def = Define `
  tick_before vs f s =
    if s.clock = 0 then (s,F) else f (delete_vars vs (dec_clock s))`

val Corr_Loop_lemma = prove(
  ``(!s. Corr (LoopBody p) s (INR (f s)) (q s)) ==>
    Corr (Loop vs p) s (INR (f (delete_vars vs (dec_clock s))))
                       (q (delete_vars vs (dec_clock s)) /\ s.clock <> 0)``,
  fs [Corr_def] \\ rw []
  \\ once_rewrite_tac [eval_cases] \\ fs []
  \\ qpat_x_assum `!x. _` imp_res_tac \\ rfs []);

val Corr_Loop = MATCH_MP Corr_Loop_lemma (Corr_LoopBody |> UNDISCH) |> DISCH_ALL;

val Corr_STRENGTHEN_TERM = prove(
  ``Corr p s f q ==>
    !f' q'.
      (q' ==> (f = INR f') /\ q) ==>
      Corr p s (INR f') q'``,
  rw [Corr_def] \\ fs []);

(* derive Corr thm from AST *)

val dec_clock_thm = prove(
  ``dec_clock s = clock_write (s.clock - 1) s``,
  EVAL_TAC);

val array_write_cancel = store_thm("array_write_cancel[simp]",
  ``array_write n (s.arrays n) s = s``,
  fs [array_write_def,fetch "-" "state_component_equality",
      APPLY_UPDATE_THM,FUN_EQ_THM]);

val reg_write_cancel = store_thm("reg_write_cancel[simp]",
  ``(n IN FDOM s.regs ==> reg_write n (SOME (s.regs ' n)) s = s) /\
    (~(n IN FDOM s.regs) ==> reg_write n NONE s = s)``,
  fs [reg_write_def,fetch "-" "state_component_equality",
      FAPPLY_FUPDATE_THM,fmap_EXT,EXTENSION,DOMSUB_FAPPLY_THM]
  \\ rw[] \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs []
  \\ strip_tac \\ fs []);

val state_eq_lemma = prove(
  ``(s0 = s1) <=>
    s0.clock = s1.clock /\
    FDOM s0.regs = FDOM s1.regs /\
    (!n. n IN FDOM s0.regs ==> s0.regs ' n = s1.regs ' n) /\
    (!n. s0.arrays n = s1.arrays n)``,
  fs [fetch "-" "state_component_equality",fmap_EXT,FUN_EQ_THM]
  \\ rw [] \\ eq_tac \\ rw []);

val clock_write_simp = store_thm("clock_write_simp[simp]",
  ``(clock_write n s).regs = s.regs /\
    (clock_write n s).arrays = s.arrays /\
    (clock_write n s).clock = n``,
  fs [clock_write_def]);

val dec_clock_write_simp = store_thm("dec_clock_simp[simp]",
  ``(dec_clock s).regs = s.regs /\
    (dec_clock s).arrays = s.arrays /\
    (dec_clock s).clock = s.clock - 1``,
  fs [dec_clock_def]);

val reg_write_simp = store_thm("reg_write_simp[simp]",
  ``(reg_write n NONE s).regs = s.regs \\ n /\
    (reg_write n (SOME w) s).regs = s.regs |+ (n,w) /\
    (reg_write n v s).arrays = s.arrays /\
    (reg_write n v s).clock = s.clock``,
  Cases_on `v` \\ fs [reg_write_def]);

val reg_write_simp_alt = store_thm("reg_write_simp_alt",
  ``((reg_write n NONE s).regs ' m = if n = m then FEMPTY ' m else s.regs ' m) /\
    ((reg_write n (SOME w) s).regs ' m = if n = m then w else s.regs ' m) /\
    (FDOM (reg_write n NONE s).regs = FDOM s.regs DELETE n) /\
    (FDOM (reg_write n (SOME w) s).regs = n INSERT FDOM s.regs)``,
  fs [reg_write_def,DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM] \\ rw []);

val array_write_simp = store_thm("array_write_simp[simp]",
  ``(array_write n w s).regs = s.regs /\
    (array_write n w s).arrays = (n =+ w) s.arrays /\
    (array_write n w s).clock = s.clock``,
  fs [array_write_def]);

val delete_vars_simp = store_thm("delete_vars_simp[simp]",
  ``!vs.
      (delete_vars vs s).clock = s.clock /\
      (delete_vars vs s).arrays = s.arrays /\
      (FLOOKUP (delete_vars vs s).regs n =
         if MEM n vs then NONE else FLOOKUP s.regs n) /\
      ((n IN FDOM (delete_vars vs s).regs) =
         if MEM n vs then F else (n IN FDOM s.regs))``,
  Induct \\ fs [delete_vars_def,FLOOKUP_DEF]
  \\ rw [DOMSUB_FAPPLY_THM] \\ fs []
  \\ eq_tac \\ rw []);

val write_simps = LIST_CONJ [array_write_simp, reg_write_simp,
  dec_clock_write_simp, clock_write_simp]

val FLOOKUP_DOMSUB = store_thm("FLOOKUP_DOMSUB[simp]",
  ``FLOOKUP (f \\ n) m = if m = n then NONE else FLOOKUP f m``,
  fs [FLOOKUP_DEF] \\ rw [] \\ fs [DOMSUB_FAPPLY_THM]);

val s_var = Corr_def |> concl |> dest_forall |> snd |> dest_forall |> fst

fun find_ret_tuple tm =
  if is_var tm then
    tm
  else if pairSyntax.is_pair tm then
    tm
  else if is_let tm then
    pairSyntax.dest_anylet tm |> snd |> find_ret_tuple
  else if is_cond tm then let
    val (_,x1,x2) = dest_cond tm
    in find_ret_tuple x1 handle HOL_ERR _ =>
       find_ret_tuple x2 end
  else fail()

fun get_array_name a = let
  val a = a |> dest_var |> fst
  val a = if a = "xs" then ``In1`` else
          if a = "ys" then ``In2`` else
          if a = "zs" then ``Out`` else fail()
  in a end

fun get_pat th =
  th |> SPEC_ALL |> UNDISCH_ALL |> concl |> rator |> rator |> rator |> rand;

fun D th = let
  val th1 = th |> DISCH_ALL |> PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  in if th1 |> concl |> is_imp then th1 else DISCH T th end

val const_def = el 1 (all_code_defs |> CONJUNCTS |> rev)

val simp_var_assums_conv =
  SIMP_CONV (srw_ss()) [FLOOKUP_UPDATE,APPLY_UPDATE_THM]

(* order: clock then array then reg_write *)
val sort_lemma = prove(
  ``(clock_write l1 (clock_write l2 s) = clock_write l1 s) /\
    (* array_write move inwards *)
    (array_write a1 x1 (clock_write l s) = clock_write l (array_write a1 x1 s)) /\
    (array_write a1 x1 (array_write a1 x2 s) = array_write a1 x1 s) /\
    (array_write In2 x1 (array_write In1 x2 s) =
     array_write In1 x2 (array_write In2 x1 s)) /\
    (array_write Out x1 (array_write In1 x2 s) =
     array_write In1 x2 (array_write Out x1 s)) /\
    (array_write Out x1 (array_write In2 x2 s) =
     array_write In2 x2 (array_write Out x1 s)) /\
    (* reg_write move inwards *)
    (n2 < n1 ==>
     reg_write n1 w1 (reg_write n2 w2 s) = reg_write n2 w2 (reg_write n1 w1 s)) /\
    (reg_write n1 w1 (reg_write n1 w2 s) = reg_write n1 w1 s) /\
    (reg_write n1 w1 (clock_write l s) = clock_write l (reg_write n1 w1 s)) /\
    (reg_write n1 w1 (array_write a1 x1 s) = array_write a1 x1 (reg_write n1 w1 s))``,
  Cases_on `w1`
  \\ Cases_on `w2`
  \\ rw [state_eq_lemma,EXTENSION,FAPPLY_FUPDATE_THM,array_write_def,clock_write_def]
  \\ TRY eq_tac \\ rw [] \\ CCONTR_TAC \\ fs [DOMSUB_FAPPLY_THM]
  \\ rfs [FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM]
  \\ rpt (pop_assum mp_tac) \\ rw []) |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ;

val reg_write_pat = ``reg_write n v s``
val clock_write_pat = clock_write_def |> SPEC_ALL |> concl |> lhs
val array_write_pat = array_write_def |> SPEC_ALL |> concl |> lhs
val dec_clock_pat = dec_clock_def |> SPEC_ALL |> concl |> lhs
val delete_vars_pat = ``delete_vars vs s``

local val s = HolKernel.syntax_fns2 "word_bignum" in
  val (clock_write_tm,mk_clock_write,dest_clock_write,is_clock_write) = s "clock_write"
end
local val s = HolKernel.syntax_fns3 "word_bignum" in
  val (reg_write_tm,mk_reg_write,dest_reg_write,is_reg_write) = s "reg_write"
  val (array_write_tm,mk_array_write,dest_array_write,is_array_write) = s "array_write"
end

val sort_thms = let
  val xs = sort_lemma |> CONJUNCTS |> map SPEC_ALL
  val x = first (is_imp o concl) xs
  fun up_to 0 = []
    | up_to n = n-1 :: up_to (n-1)
  fun pairs 0 = []
    | pairs n = map (fn m => (n-1,m)) (up_to (n-1)) @ pairs (n-1)
  fun f (n1,n2) =
    x |> INST [``n1:num``|->numSyntax.term_of_int n1,
               ``n2:num``|->numSyntax.term_of_int n2]
      |> SIMP_RULE std_ss []
  val ys = filter (not o is_imp o concl) xs @
             map f (pairs 23) (* all variables have names < 23 *)
  in ys end

val all_goals = ref (tl [T]);

val sort_writes_conv = let
  val raw_sort_conv = QCONV (REWRITE_CONV sort_thms)
  val cc = REWRITE_CONV [delete_vars_def,dec_clock_thm,write_simps]
  fun do_it_conv tm = let
    fun dest_writes tm =
      let
        val (l,s) = dest_clock_write tm
      in rator (mk_clock_write(genvar(type_of l),s_var)) :: dest_writes s end
      handle HOL_ERR _ =>
      let
        val (a,x,s) = dest_array_write tm
      in rator (mk_array_write(a,genvar(type_of x),s_var)) :: dest_writes s end
      handle HOL_ERR _ =>
      let
        val (a,x,s) = dest_reg_write tm
      in rator (mk_reg_write(a,genvar(type_of x),s_var)) :: dest_writes s end
      handle HOL_ERR _ => []
    val xs = dest_writes tm
    fun make_term [] = s_var
      | make_term (x::xs) = mk_comb(x,make_term xs)
    val lemma = raw_sort_conv (make_term xs)
    in REWR_CONV lemma tm end
  fun is_inl_inr_conv tm =
    if can (match_term reg_write_pat) tm
       orelse can (match_term clock_write_pat) tm
       orelse can (match_term array_write_pat) tm
    then ALL_CONV tm else NO_CONV tm
  in cc THENC ONCE_DEPTH_CONV (is_inl_inr_conv THENC do_it_conv) end

(*
val th = (Corr_Skip |> INST [s_var |-> ret_tm])
*)

fun remove_write_from_init th = let
  val tm = concl th |> rator |> rator |> rand
  val del_pat = ``delete_vars vs ^s_var``
  val xs = find_terms (can (match_term del_pat)) tm |> map (rand o rator)
             |> map (fst o listSyntax.dest_list) |> Lib.flatten
  val del_assums = map (fn tm => ``~(^tm IN FDOM ^s_var.regs)``) xs
  val reg_pat = reg_write_def |> CONJUNCT2 |> SPEC_ALL |> concl |> lhs |> rator
  val xs = find_terms (can (match_term reg_pat)) tm
  val reg_assums =
    map (fn tm => ``FLOOKUP s.regs ^(tm |> rator |> rand) = ^(tm |> rand)``) xs
  val clock_pat = clock_write_def |> SPEC_ALL |> concl |> lhs |> rator
  val xs = find_terms (can (match_term clock_pat)) tm
  val clock_assums = map (fn tm => ``^(s_var).clock = ^(tm |> rand)``) xs
  val array_pat = array_write_def |> SPEC_ALL |> concl |> lhs |> rator
  val xs = find_terms (can (match_term array_pat)) tm
  val array_assums =
    map (fn tm => ``s.arrays ^(tm |> rator |> rand) = ^(tm |> rand)``) xs
  val goal = foldr mk_imp (mk_eq(tm,s_var)) (array_assums @ del_assums @
                reg_assums @ clock_assums)
  val lemma = prove(``^goal``,
    CONV_TAC sort_writes_conv
    \\ rw [] \\ fs [FLOOKUP_DEF] \\ rw []
    \\ fs [state_eq_lemma,clock_write_def]) |> UNDISCH_ALL
  in th |> CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV) (REWR_CONV lemma)) end

val reg_read_lemma1 = prove(
  ``!v n. FLOOKUP s.regs n = SOME v ==> (n IN FDOM s.regs <=> T)``,
  fs [FLOOKUP_DEF]);

val reg_read_lemma1_pat =
  reg_read_lemma1 |> SPEC_ALL |> concl |> dest_imp |> snd |> lhs

val reg_read_lemma2 = prove(
  ``!v n. FLOOKUP s.regs n = SOME v ==> s.regs ' n = v``,
  fs [FLOOKUP_DEF]);

val reg_read_lemma2_pat =
  reg_read_lemma2 |> SPEC_ALL |> concl |> dest_imp |> snd |> lhs

val array_read_lemma = prove(
  ``!v n. s.arrays n = v ==> s.arrays n = v``,
  fs []);

val array_read_lemma_pat =
  array_read_lemma |> SPEC_ALL |> concl |> dest_imp |> snd |> lhs

val clock_read_lemma = prove(
  ``s.clock = l ==> s.clock = l``,
  fs []);

val clock_read_lemma_pat =
  clock_read_lemma |> SPEC_ALL |> concl |> dest_imp |> snd |> lhs

fun read_conv tm =
  if can (match_term reg_read_lemma1_pat) tm then let
    val n = tm |> rator |> rand
    val nn = "r" ^ int_to_string (numSyntax.int_of_term n)
    val lemma = reg_read_lemma1 |> SPECL [mk_var(nn,``:'a word``), n]
    in UNDISCH lemma end
  else if can (match_term reg_read_lemma2_pat) tm then let
    val n = tm |> rand
    val nn = "r" ^ int_to_string (numSyntax.int_of_term n)
    val lemma = reg_read_lemma2 |> SPECL [mk_var(nn,``:'a word``), n]
    in UNDISCH lemma end
  else if can (match_term clock_read_lemma_pat) tm then let
    val lemma = clock_read_lemma
    in UNDISCH lemma end
  else if can (match_term array_read_lemma_pat) tm then let
    val n = tm |> rand
    val nn = dest_const n |> fst
    val nn = if nn = "In1" then "xs" else
             if nn = "In2" then "ys" else "zs"
    val lemma = array_read_lemma |> SPECL [mk_var(nn,type_of tm), n]
    in UNDISCH lemma end
  else NO_CONV tm

fun make_new_vars th = let
  val vs = D th |> concl |> free_vars
  fun f v =
    if v = s_var then s_var |-> s_var else let
      val (n,ty) = dest_var v
      in v |-> mk_var("new_" ^ n,ty) end
  in INST (map f vs) th end

fun remove_new_vars th = let
  val vs = D th |> concl |> free_vars
  fun f v = let
    val (n,ty) = dest_var v
    in if String.isPrefix "new_" n then
         v |-> mk_var(String.substring(n,4,size(n)-4),ty)
       else v |-> v end
  in INST (map f vs) th end

fun let_intro_conv v =
   UNBETA_CONV v THENC REWR_CONV (GSYM LET_THM);

fun list_let_intro_conv [] = ALL_CONV
  | list_let_intro_conv (v::vs) =
      let_intro_conv v THENC list_let_intro_conv vs

val Corr_move_pre = prove(
  ``(b ==> Corr code s f p) <=> Corr code s f (b /\ p)``,
  fs [Corr_def] \\ Cases_on `b` \\ fs []);

val loop_app_EQ = prove(
  ``(loop_app f g x = (INR t,T) <=> f x = INR t /\ g x) /\
    (loop_app f g x = (INL t,T) <=>
       ?x'. f x = INL x' /\ dec_clock x' = t /\ g x /\ x'.clock <> 0)``,
  fs [loop_app_def] \\ Cases_on `f x` \\ fs []);

val true_pres = prove(
  ``mc_single_mul_pre (r0,r1,r2) /\
    mc_mul_by_single2_pre (r6,r7,r8) /\
    mc_cmp3_pre (r1,r2,r3,r9,r10,r11) /\
    mc_cmp_mul2_pre (r6,r7,r8,r9,r10,r11) /\
    mc_cmp2_pre (r0,r2,r10,r11) /\
    mc_adj_cmp_pre (r0,r3,r8) /\
    mc_idiv_mod_header_pre (r6,r11) /\
    mc_iadd1_pre (r1,r2,xs,ys) /\
    mc_iadd2_pre (r1,r2,r3,r4,xs,ys) /\
    mc_iadd3_pre (r1,xs,ys) /\
    mc_isub_flip_pre (r1,r2) /\
    mc_imul1_pre (r10,r11) /\
    mc_sub1_pre r6 /\ mc_cmp2_pre (r0,r2,r10,r11)``,
  fs [mc_single_mul_pre_def, mc_cmp3_pre_def, mc_cmp_mul2_pre_def,
      mc_cmp2_pre_def, mc_mul_by_single2_pre_def, mc_adj_cmp_pre_def,
      mc_sub1_pre_def, mc_cmp2_pre_def, mc_idiv_mod_header_pre_def,
      mc_iadd1_pre_def, mc_iadd2_pre_def, mc_iadd3_pre_def,
      mc_imul1_pre_def, mc_isub_flip_pre_def]
  \\ rpt (pairarg_tac \\ fs []));

val single_add_word_imp_0_1 = prove(
  ``single_add_word x1 x2 x3 = (y1,y2) ==> y2 <> 0w ==> y2 = 1w``,
  fs [single_add_word_def,multiwordTheory.single_add_def] \\ rw []
  \\ fs [multiwordTheory.b2w_def]);

fun first_let_if_conv c tm =
  if is_cond tm then
    (RATOR_CONV o RATOR_CONV o RAND_CONV) c tm
  else if can pairSyntax.dest_anylet tm then
    (RAND_CONV) c tm
  else if is_var tm then ALL_CONV tm
  else if is_const tm then ALL_CONV tm
  else if is_abs tm then ABS_CONV (first_let_if_conv c) tm
  else if is_comb tm then
    (RATOR_CONV (first_let_if_conv c) THENC
     RAND_CONV (first_let_if_conv c)) tm
  else ALL_CONV tm

val _ = diminish_srw_ss ["LET"];

fun derive_corr_thm const_def = let

  (* look up definitions *)
  val (r,l) = const_def |> concl |> dest_eq
  val name = r |> dest_const |> fst
  val name = String.substring(name,0,size(name)-5)
  val def = fetch "mc_multiword" (name ^ "_def")
  val pre_def = fetch "mc_multiword" (name ^ "_pre_def")
  val def_tail = fetch "mc_multiword" (name)
  val pre_tail = fetch "mc_multiword" (name ^ "_pre")
  val _ = print ("derive_corr_thm " ^ name ^ " \t")
  (* compute ret and cont Corr thms *)
  val inp = def |> concl |> lhs |> rand
  val out = find_ret_tuple (def |> concl |> rhs)
  val is = helperLib.list_dest pairSyntax.dest_pair inp
  val os = helperLib.list_dest pairSyntax.dest_pair out
  fun add_all_writes ws dels tm = let
    val vs = map (fn v => dest_reg v handle HOL_ERR _ => s_var) ws
    fun add_extra_writes tm = mk_comb(``(delete_vars ^dels):α state -> α state``,tm)
    fun add_writes [] tm = tm
      | add_writes (v::vs) tm = let
          val n = dest_reg v
          in add_writes vs (``reg_write ^n (SOME ^v) ^tm``) end
        handle HOL_ERR _ => let
          val _ = type_of v = ``:num`` orelse fail()
          in add_writes vs (``clock_write ^v ^tm``) end
        handle HOL_ERR _ => let
          val n = get_array_name v
          in add_writes vs (``array_write ^n ^v ^tm``) end
        handle HOL_ERR _ => failwith("add_writes should not break")
    in add_extra_writes (add_writes ws tm) end
  val del_pat = ``Seq (Delete vs) Skip:'a prog``
  val dels = find_term (can (match_term del_pat)) l |> rator |> rand |> rand
             handle HOL_ERR _ => ``[]:num list``
  val ret_tm = add_all_writes (rev os) dels s_var
  val del_pat = ``Seq (Delete vs) Continue:'a prog``
  val dels = find_term (can (match_term del_pat)) l |> rator |> rand |> rand
             handle HOL_ERR _ => ``[]:num list``
  val cont_tm = add_all_writes (rev is) dels s_var
  val skip_thm = remove_write_from_init (Corr_Skip |> INST [s_var |-> ret_tm])
  val cont_thm = remove_write_from_init (Corr_Continue |> INST [s_var |-> cont_tm])
  fun close_corr th = let
      val th = th |> DISCH_ALL |> REWRITE_RULE [flookup_thm,GSYM AND_IMP_INTRO]
                  |> UNDISCH_ALL
      val ss = filter (can dest_eq) (hyp th)
      val th = INST (map (fn tm => rhs tm |-> lhs tm) ss) th
      val th = th |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO]
      val th = th |> REWRITE_RULE [Corr_move_pre]
      in th end

  fun get_corr tm =
    if tm = Skip_tm then skip_thm else
    if tm = Continue_tm then cont_thm else
    if is_If tm then let
      val i = fst (match_term (get_pat Corr_If) tm)
      val p1 = get_corr (tm |> rator |> rand)
      val p2 = get_corr (tm |> rand)
      val th = REWRITE_RULE [eval_exp_def,eval_exp_pre_def,asmTheory.word_cmp_def,
                 eval_ri_pre_def,eval_ri_def] (INST i Corr_If)
               |> CONV_RULE (DEPTH_CONV read_conv) |> REWRITE_RULE []
      in MATCH_MP th (CONJ p1 p2) end
    else if is_Seq tm then let
      val (p1,p2) = dest_Seq tm
      val th2 = get_corr p2
      val th2 = th2 |> D |> INST [s_var |-> mk_var("t",type_of s_var)]
      val lemmas = [Corr_Assign,Corr_Delete,
                    Corr_Load,Corr_Store,Corr_Swap,
                    Corr_Add,Corr_Sub,Corr_Mul,Corr_Div] @ (!all_corrs)
      val lemma = first (fn th => can (match_term (get_pat th)) p1) lemmas
      val i = fst (match_term (get_pat lemma) p1)
      val th1 = REWRITE_RULE [eval_exp_def,eval_exp_pre_def,
                  eval_ri_pre_def,eval_ri_def] (INST i lemma)
      val th1 = CONV_RULE (DEPTH_CONV read_conv) th1
      val th1 = make_new_vars th1
      val th = MATCH_MP (MATCH_MP Corr_Seq_alt th2) th1 |> REWRITE_RULE []
      val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV) simp_var_assums_conv)
      val th = th |> PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
      val th = CONV_RULE sort_writes_conv th
      val ss = filter (fn tm => not (mem s_var (free_vars (lhs tm)))) (hyp th)
      val cc = list_let_intro_conv (map rhs ss)
      val th = th |> CONV_RULE (RAND_CONV cc THENC (RATOR_CONV o RAND_CONV) cc)
      val th = INST (map (fn tm => rhs tm |-> lhs tm) ss) th
      val th = DISCH_ALL th |> REWRITE_RULE [] |> UNDISCH_ALL
      val th = remove_new_vars th
      in th end
    else if can (match_term (get_pat Corr_Loop)) tm then let
      val i = fst (match_term (get_pat Corr_Loop) tm)
      val th = get_corr (tm |> rand)
      val th = th |> DISCH_ALL |> REWRITE_RULE [flookup_thm,GSYM AND_IMP_INTRO]
                  |> UNDISCH_ALL
      val ss = filter (can dest_eq) (hyp th)
      val th = INST (map (fn tm => rhs tm |-> lhs tm) ss) th
      val th = th |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO]
      val th = th |> REWRITE_RULE [Corr_move_pre]
      val th = th |> CONV_RULE
        (RAND_CONV (UNBETA_CONV s_var) THENC
         (RATOR_CONV o RAND_CONV) (UNBETA_CONV s_var)) |> GEN s_var
      in MATCH_MP Corr_Loop th |> INST i end
    else fail ()

  val raw_thm = get_corr l |> REWRITE_RULE [GSYM const_def] |> close_corr
  val LOOP_pat = loop_app_def |> SPEC_ALL |> concl |> lhs |> rator
  val r1 = raw_thm |> concl |> rator |> rand
  val r2 = raw_thm |> concl |> rand
  val (r1,is_rec) = (find_term (can (match_term LOOP_pat)) r1 |> rator |> rand, true)
                    handle HOL_ERR _ => (r1, false)
  val (r2,is_rec) = (find_term (can (match_term LOOP_pat)) r2 |> rand, true)
                    handle HOL_ERR _ => (r2, false)
  val v = mk_var(name ^ "_raw", type_of (mk_abs(s_var,r1)))
  val raw_def = new_definition(dest_var v |> fst, mk_eq(mk_comb(v,s_var),r1))
  val v = mk_var(name ^ "_raw_pre", type_of (mk_abs(s_var,r2)))
  val raw_pre_def = new_definition(dest_var v |> fst, mk_eq(mk_comb(v,s_var),r2))
  val corr = raw_thm |> REWRITE_RULE [GSYM raw_def,GSYM raw_pre_def]
  (* -- *)
  val inp = def |> concl |> lhs |> rand
  val out = find_ret_tuple (def |> concl |> rhs)
  val is = helperLib.list_dest pairSyntax.dest_pair inp
  val os = helperLib.list_dest pairSyntax.dest_pair out
  fun add_pres [] tm = tm
    | add_pres (v::vs) tm = let
          val n = dest_reg v
          in add_pres vs (mk_conj(``^n IN FDOM ^(s_var).regs``,tm)) end
        handle HOL_ERR _ => add_pres vs tm
  val pre_tm = add_pres (rev is) (pre_def |> concl |> lhs)
  val pre_tm = if is_rec then mk_conj(pre_tm,``(^s_var).clock <> 0``) else pre_tm
  val del_pat = ``Seq (Delete vs) Skip:'a prog``
  val dels = find_term (can (match_term del_pat)) l |> rator |> rand |> rand
             handle HOL_ERR _ => ``[]:num list``
  val cont_del_pat = ``Seq (Delete vs) Continue:'a prog``
  val cont_dels = find_term (can (match_term cont_del_pat)) l |> rator |> rand |> rand
                  handle HOL_ERR _ => ``[]:num list``
  val num_pair_pat = ``(n:num,w:'a word)``
  val reg_write_pat = ``reg_write n (w:'a word option):α state -> α state``
  fun add_all_writes ws dels tm = let
    val vs = map (fn v => dest_reg v handle HOL_ERR _ => s_var) ws
    fun add_extra_writes tm = mk_comb(``(delete_vars ^dels):α state -> α state``,tm)
    fun add_writes [] tm = tm
      | add_writes (v::vs) tm = let
          val n = dest_reg v
          in add_writes vs (``reg_write ^n (SOME ^v) ^tm``) end
        handle HOL_ERR _ => let
          val _ = type_of v = ``:num`` orelse fail()
          in add_writes vs (``clock_write ^v ^tm``) end
        handle HOL_ERR _ => let
          val n = get_array_name v
          in add_writes vs (``array_write ^n ^v ^tm``) end
        handle HOL_ERR _ => failwith("add_writes should not break")
    in add_extra_writes (add_writes ws tm) end
  val new_state =
    pairSyntax.mk_anylet ([(out,def |> concl |> lhs)],
      add_all_writes (rev os) dels s_var)
  fun let_inp [] tm = tm
    | let_inp (v::vs) tm = let
          val n = dest_reg v
          val tm = ``let ^v = (^s_var).regs ' ^n in ^tm``
          in let_inp vs tm end
        handle HOL_ERR _ => let
          val n = get_array_name v
          val tm = ``let ^v = (^s_var).arrays ^n in ^tm``
          in let_inp vs tm end
        handle HOL_ERR _ => let
          val _ = type_of v = ``:num`` orelse fail()
          val tm = ``let ^v = (^s_var).clock in ^tm``
          in let_inp vs tm end
        handle HOL_ERR _ => failwith("let_inp should not fail")
  val ii = if is_rec then subst [``l:num``|->``l-1n``] else I
  val new_post = let_inp (rev is) (ii new_state)
  val new_pre = let_inp (rev is) (ii pre_tm)
  val th = MATCH_MP Corr_STRENGTHEN_TERM corr |> SPECL [new_post,new_pre]
  val goal = th |> concl |> dest_imp |> fst

(*
  max_print_depth := 15
*)

  in
    if not is_rec then let
      val lemma = prove(``^goal``,
        CONV_TAC sort_writes_conv
        \\ full_simp_tac std_ss [def] \\ rw []
        \\ REV_FULL_SIMP_TAC std_ss [pre_def,LET_THM]
        \\ full_simp_tac std_ss [LET_THM]
        \\ REV_FULL_SIMP_TAC std_ss [pre_def,LET_THM]
        \\ rpt (pairarg_tac \\ FULL_SIMP_TAC std_ss [] \\ every_case_tac)
        \\ full_simp_tac std_ss [LET_THM] \\ rveq
        \\ REV_FULL_SIMP_TAC std_ss []
        \\ rpt (pairarg_tac \\ FULL_SIMP_TAC std_ss [] \\ every_case_tac)
        \\ asm_rewrite_tac [raw_def,INL_11,INR_11,delete_vars_def,raw_pre_def]
        \\ rpt (pop_assum mp_tac)
        \\ rpt (CHANGED_TAC
             (CONV_TAC (first_let_if_conv
               (SIMP_CONV (srw_ss())
                  [DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM]))
              \\ simp_tac std_ss []
              \\ CONV_TAC (first_let_if_conv
               (SIMP_CONV (srw_ss())
                  [DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM]))
              \\ simp_tac std_ss [Once LET_THM]))
        \\ fs [] \\ rw []
        \\ imp_res_tac single_add_word_imp_0_1
        \\ rw [] \\ TRY eq_tac \\ rw [] \\ fs [true_pres]
        \\ CONV_TAC sort_writes_conv \\ fs []
        \\ CONV_TAC sort_writes_conv \\ fs [true_pres])
      val raw_th = MP th lemma |> SIMP_RULE std_ss [LET_THM]
      val th = raw_th |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV THENC
                                    sort_writes_conv)
      val _ = save_thm(name ^ "_corr_thm", raw_th)
      val _ = (all_corrs := th::(!all_corrs))
      in (def,raw_th) end
    else let

      val tm = add_all_writes (rev is) cont_dels ``s0:'a state``
      val r = pairSyntax.mk_pabs(inp,``\s. s = ^tm``)
      val tm = add_all_writes (rev os) dels ``s0:'a state``
      val p = pairSyntax.mk_pabs(out,``\s. s = ^tm``)
      val loop_app_tm = loop_app_def
        |> ISPEC (raw_def |> SPEC_ALL |> concl |> lhs)
        |> ISPEC (raw_pre_def |> SPEC_ALL |> concl |> lhs)
        |> SPEC_ALL |> concl |> lhs |> rator
      val th1 =
        SHORT_TAILREC_SIM
        |> ISPEC (def_tail |> concl |> rand |> rand)
        |> REWRITE_RULE [GSYM def_tail, GSYM pre_tail]
        |> ISPEC loop_app_tm |> SIMP_RULE std_ss [loop_app_EQ,PULL_EXISTS]
        |> SPEC r |> SPEC p
      val goal1 = th1 |> concl |> dest_imp |> fst

      val lemma1 = prove(``^goal1``,
        CONV_TAC sort_writes_conv
        \\ strip_tac \\ TRY (PairCases_on `x`) \\ fs [loop_app_EQ]
        \\ rpt (pairarg_tac \\ full_simp_tac std_ss []) \\ rveq
        \\ rpt TOP_CASE_TAC \\ rveq
        \\ simp_tac std_ss []
        \\ rewrite_tac [raw_def,raw_pre_def,delete_vars_def,dec_clock_thm]
        \\ simp_tac std_ss [PULL_EXISTS,write_simps,FDOM_FUPDATE,IN_INSERT,
                DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM,true_pres]
        \\ rpt (CHANGED_TAC
             (CONV_TAC (first_let_if_conv
               (SIMP_CONV (srw_ss())
                  [DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM]))
              \\ simp_tac std_ss []
              \\ CONV_TAC (first_let_if_conv
               (SIMP_CONV (srw_ss())
                  [DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM]))
              \\ simp_tac std_ss [Once LET_THM]))
        \\ simp_tac (srw_ss()) [DOMSUB_FAPPLY_THM,true_pres,
             FAPPLY_FUPDATE_THM,EXTENSION,APPLY_UPDATE_THM]
        \\ CONV_TAC sort_writes_conv \\ fs [true_pres]
        \\ CONV_TAC sort_writes_conv \\ fs [true_pres])

      val th1 = MP th1 lemma1
      val lemma = prove(``^goal``,
        fs [LET_DEF] \\ rpt strip_tac \\ rw [] \\ fs []
        \\ drule (GEN_ALL th1) \\ fs []
        \\ pairarg_tac \\ fs []
        \\ disch_then (qspecl_then [`s`,`s`] strip_assume_tac) \\ fs []
        \\ rfs [dec_clock_thm])
      val raw_th = MP th lemma |> SIMP_RULE std_ss [LET_THM]
      val th = raw_th |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV THENC
                                    sort_writes_conv)
      val _ = save_thm(name ^ "_corr_thm", raw_th)
      val _ = (all_corrs := th::(!all_corrs))
      in (def,raw_th) end
  end;

val const_def = time (first (not o time (can derive_corr_thm)))
                     (all_code_defs |> CONJUNCTS |> rev)
                handle HOL_ERR _ => TRUTH;

val _ = (concl const_def = T) orelse failwith "derive_corr_thm failed";

(*

val th = fetch "-" "mc_iop_corr_thm"
  |> REWRITE_RULE [Corr_def] |> UNDISCH_ALL
  |> MATCH_MP compile_thm
  |> SIMP_RULE (srw_ss()) [SIMP_RULE std_ss [] (EVAL ``syntax_ok mc_iop_code``)]
  |> SPEC_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO]

*)

val _ = export_theory();
