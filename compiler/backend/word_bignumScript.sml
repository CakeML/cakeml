(*
  The bignum library used by the CakeML compiler. Note that the
  implementation is automatically generated from a shallow embedding
  that is part of the HOL distribution in mc_multiwordTheory.
*)
open preamble astTheory wordLangTheory mc_multiwordTheory;

val _ = new_theory "word_bignum";


(* syntax of a little language *)

val _ = Datatype `
  address = In1 | In2 | Out`

val _ = Datatype `
  mini = Skip
       | Assign num ('a wordLang$exp)
       | Delete (num list)
       | Seq mini mini
       | Load num num address
       | Store num num
       | If cmp num ('a reg_imm) mini mini
       | Swap
       | Add num num num ('a reg_imm) ('a reg_imm)
       | Sub num num num ('a reg_imm) ('a reg_imm)
       | Mul num num num num
       | Div num num num num num
       | Loop bool (num list) mini
       | Continue
       | Rec (num list) (num list)
       (* the following is only used by the semantics *)
       | LoopBody mini `


(* syntax helper funs *)

val Skip_tm = ``Skip:'a word_bignum$mini``
val Swap_tm = ``Swap:'a word_bignum$mini``
val Continue_tm = ``Continue:'a word_bignum$mini``

local val s = HolKernel.syntax_fns1 "word_bignum" in
  val (Delete_tm,mk_Delete,dest_Delete,is_Delete) = s "Delete"
end
local val s = HolKernel.syntax_fns2 "word_bignum" in
  val (Assign_tm,mk_Assign,dest_Assign,is_Assign) = s "Assign"
  val (Rec_tm,mk_Rec,dest_Rec,is_Rec) = s "Rec"
  val (Seq_tm,mk_Seq,dest_Seq,is_Seq) = s "Seq"
  val (Store_tm,mk_Store,dest_Store,is_Store) = s "Store"
end
local val s = HolKernel.syntax_fns3 "word_bignum" in
  val (Loop_tm,mk_Loop,dest_Loop,is_Loop) = s "Loop"
  val (Load_tm,mk_Load,dest_Load,is_Load) = s "Load"
end

local val s = HolKernel.syntax_fns1 "asm" in
  val (Imm_tm,mk_Imm,dest_Imm,is_Imm) = s "Imm"
  val (Reg_tm,mk_Reg,dest_Reg,is_Reg) = s "Reg"
end

val If_pat = ``word_bignum$If c r (ri:'a reg_imm) p1 p2``
fun dest_If tm = let
  val i = fst (match_term If_pat tm)
  fun list_dest f tm = let
    val (x,y) = f tm
    in list_dest f x @ list_dest f y end handle HOL_ERR _ => [tm]
  val ts = list_dest dest_comb If_pat
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
  in wordLangSyntax.mk_Shift(name,x1,``^x2``) end
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
    val _ = (v ~~ rand r) orelse fail ()
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
    val xs = find_terms is_const x
             |> filter (fn x => #Thy (dest_thy_const x) <> "pair")
    val _ = length xs = 0 orelse fail()
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

fun dest_tuple tm = let
  val (x,y) = dest_pair tm
  in dest_tuple x @ dest_tuple y end
  handle HOL_ERR _ => [tm];

fun get_full_prog inp tm = let
  val immediate_deps = ref ([]:term list);
  val ret_tm = ref Skip_tm;
  val cont_tm = ref Continue_tm;
  val ret_vars = ref ([]:term list);
  val cont_vars = ref ([]:term list);
  (* helpers *)
  fun dest_num_let tm =
    if (dest_let tm |> snd |> type_of) = ``:num`` then
      dest_let tm |> fst |> dest_abs |> snd else fail ()
  fun dest_num_if tm = let
    val (x,y,z) = dest_cond tm
    val (l,r) = dest_eq x
    in if type_of l = ``:num`` then z else fail () end
  fun dest_num_let_or_if tm =
    dest_num_if tm handle HOL_ERR _ => dest_num_let tm
  fun dest_rec_let tm = let
    val ((_,y),rest) = my_dest_let tm
    val (saves,call) = dest_pair y
    in (saves,call,rest) end
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
    (* recursive let *) let
    val (saves,call,rest) = dest_rec_let tm
    val saves = saves |> dest_tuple |> map dest_reg
    val saves = listSyntax.mk_list(saves,``:num``)
    val dels = listSyntax.mk_list([],``:num``)
    val _ = (cont_vars := free_vars call)
    in mk_Seq(mk_Rec(saves,dels),get_prog rest) end handle HOL_ERR _ =>
    (* If *) let
    val (b,t1,t2) = dest_cond tm
    val (x1,x2,x3) = get_guard b
    in mk_If(x1,x2,x3,get_prog t1,get_prog t2) end handle HOL_ERR _ =>
    if is_const (rator tm) andalso (is_var (rand tm) orelse is_pair (rand tm))
    then (cont_vars := free_vars tm; !cont_tm) else
    if can dest_num_let_or_if tm then get_prog (dest_num_let_or_if tm) else
    let
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
             |> filter (fn tm => tmem (lhs (concl tm)) (!immediate_deps)
                                 handle HOL_ERR _ => true)
             |> LIST_CONJ |> CONJ (REFL init_prog) |> concl
  fun is_delete tm =
    can (match_term ``(Delete n):'a mini``) tm
  val Add_tm = ``(Add n1 n2):num -> α reg_imm -> α reg_imm -> α mini``
  val Sub_tm = ``(Sub n1 n2):num -> α reg_imm -> α reg_imm -> α mini``
  val Mul_tm = ``(Mul n1 n2):num -> num -> α mini``
  val Div_tm = ``(Div n1 n2):num -> num -> num -> α mini``
  fun is_assign tm =
    can (match_term ``(Assign n):α wordLang$exp -> α mini``) tm orelse
    can (match_term ``(Load n):num -> address -> α mini``) tm orelse
    can (match_term Add_tm) tm orelse can (match_term (rator Add_tm)) tm orelse
    can (match_term Sub_tm) tm orelse can (match_term (rator Sub_tm)) tm orelse
    can (match_term Mul_tm) tm orelse can (match_term (rator Mul_tm)) tm orelse
    can (match_term Div_tm) tm orelse can (match_term (rator Div_tm)) tm
  fun f tm = dest_reg tm handle HOL_ERR _ => tm
  val ds = op_mk_set aconv ((find_terms is_assign x |> map rand) @
                       (find_terms is_delete x
                            |> map (fst o listSyntax.dest_list o rand)
                            |> flatten) @
                       filter (not o is_var) (map f (free_vars inp)))
  fun add_dels [] tm = tm
    | add_dels vs tm = mk_Seq (mk_Delete (listSyntax.mk_list(vs,type_of (hd vs))), tm)
  val _ = (ret_tm := add_dels (op_set_diff aconv ds (map f (!ret_vars))) Skip_tm)
  val cont_dels = (op_set_diff aconv ds (map f (!cont_vars)))
  val _ = (cont_tm := add_dels cont_dels Continue_tm)
  in (listSyntax.mk_list(cont_dels,``:num``),get_prog tm) end

fun to_deep def = let
  (* produce deep embedding *)
  val f = def |> SPEC_ALL |> concl |> dest_eq |> fst |> repeat rator
  val tm = def |> SPEC_ALL |> concl |> rand
  val inp = def |> SPEC_ALL |> concl |> rator |> rand |> rand
  val is_rec = can (find_term (aconv f)) tm
  fun loop () =
    get_full_prog inp tm
    handle UnableToTranslate str =>
      (to_deep (find (str ^ "_def") |> hd |> snd |> fst);
       loop ())
  val (dels,deep) = loop ()
  val rec_flag = if can (find_term is_Rec) deep then T else F
  val deep = if is_rec then mk_Loop (rec_flag,dels,deep) else deep
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

(* an example that produces Rec *)

val def = mc_fac_init_def |> to_deep
val def = mc_fac_final_def |> to_deep
val def = mc_fac_def |> to_deep
val def = mc_use_fac_def |> to_deep

(* compiler into wordLang *)

val has_compiled_def = Define `
  has_compiled code (n,code_list) =
    case ALOOKUP code_list code of
    | NONE => INR (n:num)
    | SOME (index,word_code) => INL (index:num)`;

val code_acc_next_def = Define `
  code_acc_next (n,code_list) = (n+1n,code_list)`

val install_def = Define `
  install c (n,code_list) = (n,c::code_list)`

val compile_exp_def = Define `
  compile_exp (Op b [x1;x2]) = Op b [compile_exp x1; compile_exp x2] /\
  compile_exp (Var n) = Lookup (Temp (n2w n)) /\
  compile_exp (Const w) = Const w /\
  compile_exp (Shift sh x na) = Shift sh (compile_exp x) na /\
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
           Shift Lsl (Lookup (Temp (n2w r))) (shift (:'a))])) p
              :'a wordLang$prog`

val div_location_def = Define `
  div_location = 21n`;

val DivCode_def = Define `
  DivCode l1 l2 n1 n2 n3 n4 n5 =
    MustTerminate
      (Seq (Call (SOME (n1,LS (),Skip,l1,l2)) (SOME div_location) [n3;n4;n5] NONE)
           (Assign n2 (Lookup (Temp 28w))))`

val LoadRegs_def = Define `
  (LoadRegs [] p = p:'a wordLang$prog) /\
  (LoadRegs (n::ns) p = Seq (Get (n+2) (Temp (n2w n))) (LoadRegs ns p))`

val SaveRegs_def = Define `
  (SaveRegs [] = Skip:'a wordLang$prog) /\
  (SaveRegs (n::ns) = Seq (Set (Temp (n2w n)) (Var (n+2))) (SaveRegs ns))`;

val compile_def = Define `
  (compile n l i cs Skip = (wordLang$Skip,l,i,cs)) /\
  (compile n l i cs Continue = (Call NONE (SOME n) [0] NONE,l,i,cs)) /\
  (compile n l i cs (Rec save_regs names) =
     (LoadRegs save_regs
       (Call (SOME (1,list_insert (0::MAP (\n.n+2) save_regs) LN,
          SaveRegs save_regs,n,l)) (SOME n) [] NONE),l+1,i,cs)) /\
  (compile n l i cs (Loop rec_calls vs body) =
     case has_compiled body cs of
     | INL existing_index =>
         (Call (SOME (i,LS (),Skip,n,l)) (SOME existing_index) [] NONE,l+1,i+1,cs)
     | INR new_index =>
         let (new_code,a,b,cs) = compile new_index 1 1 (code_acc_next cs) body in
           (Call (SOME (i,LS (),Skip,n,l)) (SOME new_index) [] NONE,l+1,i+1,
            install (body,new_index,new_code) cs)) /\
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
     (Seq (DivCode n l (i+0) (i+1) (i+2) (i+3) (i+4))
     (Seq (Set (Temp (n2w r0)) (Var (i+0)))
          (Set (Temp (n2w r1)) (Var (i+1))))))),l+1,i+5,cs)) /\
  (compile n l i cs _ = (Skip,l,i,cs))`

val _ = (max_print_depth := 25);

val generated_bignum_stubs_def = Define `
  generated_bignum_stubs n =
    let (x1,_,_,(_,cs)) = compile n 2 1 (n+1,[]) mc_iop_code in
      (n,1n,Seq x1 (Return 0 0)) :: MAP (\(x,y,z). (y,1,Seq z (Return 0 0))) cs`

val generated_bignum_stubs_eq = save_thm("generated_bignum_stubs_eq",
  EVAL ``generated_bignum_stubs n`` |> SIMP_RULE std_ss [GSYM ADD_ASSOC]);

val _ = export_theory();
